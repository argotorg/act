{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TypeApplications #-}

module Act.HEVM where

import Prelude hiding (GT, LT)

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List
import Data.Containers.ListUtils (nubOrd)
import qualified Data.Text as T
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as B8 (pack)
import Data.ByteString (ByteString)
import Data.Text.Encoding (encodeUtf8)
import Control.Concurrent.Async
import Control.Monad
import Data.Foldable (sequenceA_, traverse_)
import Data.DoubleWord
import Data.Maybe
import Control.Monad.State
import Data.List.NonEmpty qualified as NE
import Data.Validation
import qualified Data.Vector as V
import Data.Bifunctor

import Act.HEVM_utils
import Act.Syntax.TypedExplicit as Act
import Act.Syntax
import Act.Error
import qualified Act.Syntax.Typed as TA
import Act.Syntax.Timing
import Act.Bounds

import EVM.ABI (Sig(..))
import qualified EVM hiding (bytecode)
import qualified EVM.Types as EVM hiding (FrameState(..))
import EVM.Types (concatMapM)
import EVM.Expr hiding (op2, inRange, div, xor, not, readStorage, Array)
import EVM.SymExec hiding (isPartial, reachable)
import EVM.SMT (assertProps)
import EVM.Solvers
import EVM.Effects
import EVM.Format as Format
import EVM.Traversals
import Debug.Trace
import qualified Data.Bifunctor as Bifunctor

type family ExprType a where
  ExprType 'AInteger  = EVM.EWord
  ExprType 'ABoolean  = EVM.EWord
  ExprType 'AContract = EVM.EWord
  ExprType 'AByteStr  = EVM.Buf

-- | The storage layout. Maps each contract type to a map that maps storage
-- variables to their slot, offset, and size in bytes in memory
-- For mappings and arrays, the size refers the type after full index saturation
type Layout = M.Map Id (LayoutMode, M.Map Id (Int,Int,Int))

data LayoutMode = SolidityLayout | VyperLayout

type ContractMap = M.Map (EVM.Expr EVM.EAddr) (EVM.Expr EVM.EContract, Id)

-- | For each contract in the Act spec, put in a codemap its Act
-- specification, init code, and runtimecode. This is being looked up
-- when we encounter a constructor call.
type CodeMap = M.Map Id (Contract, BS.ByteString, BS.ByteString)

type EquivResult = EVM.ProofResult (String, EVM.SMTCex) String

initAddr :: EVM.Expr EVM.EAddr
initAddr = EVM.SymAddr "entrypoint"

slotMap :: StorageTyping -> M.Map Id LayoutMode -> Layout
slotMap store lmap =
  M.mapWithKey (\cid cstore ->
      let vars = sortOn (snd . snd) $ M.toList cstore
          layoutMode = fromJust $ M.lookup cid lmap
      in
      (layoutMode, M.fromList $ traceShowId $ makeLayout layoutMode vars 0 0)
  ) store

makeLayout :: LayoutMode -> [(String, (ValueType, Integer))] -> Int -> Int -> [(Id, (Int,Int,Int))]
makeLayout _ [] _ _ = []
makeLayout SolidityLayout ((name,(typ,_)):vars) offset slot =
  if itFits then
    (name, (slot, offset, size)):makeLayout SolidityLayout vars (offset+size) slot
  else
    (name, (slot+1, 0, size)):makeLayout SolidityLayout vars size (slot+1)
  where
    size = sizeOfValue typ
    itFits = size <= 32 - offset
makeLayout VyperLayout ((name,_):vars) _ slot =
  (name, (slot, 0, 32)):makeLayout VyperLayout vars 0 (slot+1)

-- size of a storage item in bytes
sizeOfValue :: ValueType -> Int
sizeOfValue (ValueType t) = sizeOfTValue t

sizeOfTValue :: TValueType a -> Int
sizeOfTValue (TMapping _ _) = 32
sizeOfTValue t = sizeOfAbiType $ toAbiType t

sizeOfAbiType :: AbiType -> Int
sizeOfAbiType (AbiUIntType s) = s `div` 8
sizeOfAbiType (AbiIntType s) = s `div` 8
sizeOfAbiType AbiAddressType = 20
sizeOfAbiType AbiBoolType = 1
sizeOfAbiType (AbiBytesType s) = s
sizeOfAbiType AbiBytesDynamicType = 32
sizeOfAbiType AbiStringType = 32
sizeOfAbiType (AbiArrayDynamicType _) = 32
sizeOfAbiType (AbiArrayType s t) = s * sizeOfAbiType t
sizeOfAbiType (AbiTupleType v) = V.foldr ((+) . sizeOfAbiType) 0 v
sizeOfAbiType AbiFunctionType = 0 --


-- * Act state monad

data ActEnv = ActEnv
  { codemap :: CodeMap
  , fresh   :: Int
  , layout  :: Layout
  , caddr   :: EVM.Expr EVM.EAddr
  , caller  :: Maybe (EVM.Expr EVM.EAddr)
  }

type ActT m a = StateT ActEnv m a

getCodemap :: Monad m => ActT m CodeMap
getCodemap = do
  env <- get
  pure env.codemap

getFreshIncr :: Monad m => ActT m Int
getFreshIncr = do
  env <- get
  let fresh = env.fresh
  put (env { fresh = fresh + 1 })
  pure (fresh + 1)

getFresh :: Monad m => ActT m Int
getFresh = do
  env <- get
  pure env.fresh

getLayout :: Monad m => ActT m Layout
getLayout = do
  env <- get
  pure env.layout

getCaddr :: Monad m => ActT m (EVM.Expr EVM.EAddr)
getCaddr = do
  env <- get
  pure env.caddr

localCaddr :: Monad m => EVM.Expr EVM.EAddr -> ActT m a -> ActT m a
localCaddr caddr m = do
  env <- get
  let caddr' = env.caddr
  let caller' = env.caller
  put (env { caddr = caddr, caller = Just caddr' })
  res <- m
  env' <- get
  put (env' { caddr = caddr', caller =  caller' })
  pure res

getCaller :: Monad m => ActT m (EVM.Expr EVM.EAddr)
getCaller = do
  env <- get
  case env.caller of
    Just c -> pure c
    Nothing -> pure $ EVM.SymAddr "caller" -- Zoe: not sure what to put here


-- * Act translation

storageBounds :: forall m . Monad m => ContractMap -> [TypedRef] -> ActT m [EVM.Prop]
storageBounds contractMap locs = do
  -- TODO what env should we use here?
  mapM (toProp contractMap emptyEnv) $ mkRefsBounds $ filter (not . locInCalldata) locs
  where
    locInCalldata :: TypedRef -> Bool
    locInCalldata (TRef _ _ ref) = refInCalldata ref

    refInCalldata :: Ref k -> Bool
    refInCalldata (CVar _ _ _) = True
    refInCalldata (SVar _ _ _ _) = False
    refInCalldata (RArrIdx _ r _ _) = refInCalldata r
    refInCalldata (RMapIdx _ _ _) = False
    refInCalldata (RField _ _ _ _) = False


translateConstructor :: Monad m => BS.ByteString -> Constructor -> ContractMap -> ActT m ([(EVM.Expr EVM.End, ContractMap)], Calldata, Sig, [EVM.Prop])
translateConstructor bytecode (Constructor cid iface _ preconds cases _ _) cmap = do
  let initmap = M.insert initAddr (initcontract, cid) cmap
  -- After `addBounds`, `preconds` contains all integer locations that have been constrained in the Act spec.
  -- All must be enforced again to avoid discrepancies. Necessary for Vyper.
  -- Note that since all locations are already in `preconds`,
  -- there is no need to look at other fields.
  bounds <- storageBounds initmap $ nub $ concatMap locsFromConstrCase cases <> concatMap locsFromExp preconds
  ends <- mapM (translateConstructorCase bytecode initmap (snd calldata) bounds preconds) cases
  pure (concat ends, calldata, ifaceToSig cid iface, bounds)
  where
    calldata = makeCtrCalldata iface
    initcontract = EVM.C { EVM.code    = EVM.RuntimeCode (EVM.ConcreteRuntimeCode bytecode)
                         , EVM.storage = EVM.ConcreteStore mempty
                         , EVM.tStorage = EVM.ConcreteStore mempty
                         , EVM.balance = EVM.Lit 0
                         , EVM.nonce   = Just 1
                         }

translateConstructorCase :: Monad m => BS.ByteString -> ContractMap -> [EVM.Prop] -> [EVM.Prop] -> [Exp ABoolean] -> Ccase -> ActT m (EVM.Expr EVM.End, ContractMap)
translateConstructorCase bytecode initmap cdataprops bounds preconds (Case _ casecond upds) = do
  preconds' <- mapM (toProp initmap emptyEnv) preconds
  casecond' <- toProp initmap emptyEnv casecond
  cmaps' <- applyUpdates initmap initmap emptyEnv upds
  forM cmaps' $ \(cmap',cs) -> do
    let acmap = abstractCmap initAddr cmap'
    pure (simplify $ EVM.Success (cdataprops <> preconds' <> bounds <> [casecond'] <> cs <> symAddrCnstr acmap) mempty (EVM.ConcreteBuf bytecode) (M.map fst cmap'), acmap)

symAddrCnstr :: ContractMap -> [EVM.Prop]
symAddrCnstr cmap =
    (\(a1, a2) -> EVM.PNeg (EVM.PEq (EVM.WAddr a1) (EVM.WAddr a2))) <$> comb (M.keys cmap)

translateBehvs :: Monad m => ContractMap -> [Behaviour] -> ActT m [(Id, [(EVM.Expr EVM.End, ContractMap)], Calldata, Sig, [EVM.Prop])]
translateBehvs cmap behvs = do
  --let groups = (groupBy sameIface behvs) :: [[Behaviour]]
  mapM (translateBehv cmap) behvs
  --mapM (\behvs' -> do
  --         let calldata = behvCalldata behvs'
  --         exprs <- mapM (translateBehv cmap (snd calldata) bounds) behvs'
  --         pure (behvName behvs', exprs, calldata, behvSig behvs, bounds)) groups
  --where
  --  behvCalldata (Behaviour _ _ iface _ _ _) = makeCalldata iface
  --  --behvCalldata [] = error "Internal error: behaviour groups cannot be empty"

  --  behvSig (Behaviour _ _ iface _ _ _) = ifaceToSig iface
  --  --behvSig [] = error "Internal error: behaviour groups cannot be empty"

  --  -- TODO remove reduntant name in behaviors
  --  sameIface (Behaviour _ _ iface  _ _ _) (Behaviour _ _ iface' _ _ _) =
  --    makeIface iface == makeIface iface'

  --  behvName (Behaviour _ _ (Interface name _) _ _ _) = name
  --  --behvName [] = error "Internal error: behaviour groups cannot be empty"

ifaceToSig :: Id -> Interface -> Sig
ifaceToSig name (Interface _ args) = Sig (T.pack name) (fmap fromdecl args)
  where
    fromdecl (Arg argtype _) = argToAbiType argtype

translateBehv :: Monad m => ContractMap -> Behaviour -> ActT m (Id, [(EVM.Expr EVM.End, ContractMap)], Calldata, Sig, [EVM.Prop])
translateBehv cmap (Behaviour behvName _ iface _ preconds cases _)  = do
  -- We collect all integer bounds from all cases of a given behaviour.
  -- These bounds are set as preconditions for all cases of a behaviour,
  -- even if some are not necessary for all cases, because the input space
  -- must be compared against that of the symbolic execution. On that side,
  -- it is not possible to distinguish between cases, so we make no distinction
  -- here either.
  bounds <- storageBounds cmap $ nub $ concatMap locsFromCase cases <> concatMap locsFromExp preconds
  ends <- mapM (translateBehvCase cmap (snd behvCalldata) bounds preconds) cases
  pure (behvName, concat ends, behvCalldata, behvSig, bounds)
  where
    behvCalldata = makeCalldata behvName iface
    behvSig = ifaceToSig behvName iface

translateBehvCase :: Monad m => ContractMap -> [EVM.Prop] -> [EVM.Prop] -> [Exp ABoolean] -> Bcase -> ActT m (EVM.Expr EVM.End, ContractMap)
translateBehvCase cmap cdataprops bounds preconds (Case _ casecond (upds, ret)) = do
  preconds' <- mapM (toProp cmap emptyEnv) preconds
  casecond' <- toProp cmap emptyEnv casecond
  ret' <- returnsToExpr cmap emptyEnv ret
  cmaps' <- applyUpdates cmap cmap emptyEnv upds
  forM cmaps' $ \(cmap', cs) -> do
    let acmap = abstractCmap initAddr cmap'
    pure (simplify $ EVM.Success (preconds' <> bounds <> [casecond'] <> cs <> cdataprops <> symAddrCnstr cmap') mempty ret' (M.map fst cmap'), acmap)


refToRHS :: Ref k -> Ref RHS
refToRHS (SVar p t i ci) = SVar p t i ci
refToRHS (CVar p t i) = CVar p t i
refToRHS (RMapIdx p r i) = RMapIdx p r i
refToRHS (RArrIdx p r i n) = RArrIdx p (refToRHS r) i n
refToRHS (RField p r i n) = RField p (refToRHS r) i n

-- TODO: move this if it even survives
expandMappingUpdate :: TypedRef -> Exp AMapping -> [(TypedRef, TypedExp)]
expandMappingUpdate ref (Mapping _ keyType@VType valType@VType es) =
  let refPairs = (\(k,v) -> (TRef valType SRHS (RMapIdx nowhere ref (TExp keyType k)), v)) <$> es in
  case toSType valType of
    SMapping -> concatMap (uncurry expandMappingUpdate) refPairs
    _ -> map (Bifunctor.second (TExp valType)) refPairs
expandMappingUpdate (TRef _ _ r) (MappingUpd _ r' _ _ _) | refToRHS r /= refToRHS r' =
  error "Mapping update reference inconsistency, past typing"
expandMappingUpdate ref (MappingUpd _ _ keyType@VType valType@VType es) =
  let refPairs = (\(k,v) -> (TRef valType SRHS (RMapIdx nowhere ref (TExp keyType k)), v)) <$> es in
  case toSType valType of
    SMapping -> concatMap (uncurry expandMappingUpdate) refPairs
    _ -> map (Bifunctor.second (TExp valType)) refPairs
expandMappingUpdate _ e@(ITE _ _ _ _) = error $ "Internal error: expecting flat expression. got: " <> show e
expandMappingUpdate _ (VarRef _ _ _) = error "Internal error: variable assignment of mappings not expected"

applyUpdates :: Monad m => ContractMap -> ContractMap -> CallEnv -> [StorageUpdate] -> ActT m [(ContractMap, [EVM.Prop])]
applyUpdates readMap writeMap callenv upds = foldM (\wms upd -> concatMapM (\(wm,cs) -> (fmap $ second (cs ++)) <$> applyUpdate readMap wm callenv upd) wms) [(writeMap,[])] upds

applyUpdate :: Monad m => ContractMap -> ContractMap -> CallEnv -> StorageUpdate -> ActT m [(ContractMap, [EVM.Prop])]
applyUpdate readMap writeMap callenv (Update typ@VType ref e) = writeToRef readMap writeMap callenv (TRef typ SLHS ref) (TExp typ e)

writeToRef :: Monad m => ContractMap -> ContractMap -> CallEnv -> TypedRef -> TypedExp -> ActT m [(ContractMap, [EVM.Prop])]
writeToRef readMap writeMap callenv tref@(TRef _ _ ref) (TExp typ e) = do
  caddr' <- baseAddr writeMap callenv ref
  (addr, offset, size, lmode) <- refOffset writeMap callenv ref
  let (contract, cid) = fromMaybe (error $ "Internal error: contract not found\n" <> show e) $ M.lookup caddr' writeMap
  case typ of
    TAddress | isCreate e -> do
        fresh <- getFreshIncr
        let freshAddr = EVM.SymAddr $ "freshSymAddr" <> (T.pack $ show fresh)
        writeMap' <- localCaddr freshAddr $ createCastedContract readMap writeMap callenv freshAddr e
        pure $ first (M.insert caddr' (updateNonce (updateStorage (EVM.SStore addr (EVM.WAddr freshAddr)) contract), cid)) <$> writeMap'
    TContract _ | isCreate e -> do
        fresh <- getFreshIncr
        let freshAddr = EVM.SymAddr $ "freshSymAddr" <> (T.pack $ show fresh)
        writeMap' <- localCaddr freshAddr $ createContract readMap writeMap callenv freshAddr e
        pure $ first (M.insert caddr' (updateNonce (updateStorage (EVM.SStore addr (EVM.WAddr freshAddr)) contract), cid)) <$> writeMap'
    TContract _ -> do
        e' <- toExpr readMap callenv e
        let prevValue = readStorage addr contract
        let e'' = storedValue e' prevValue offset size
        pure [(M.insert caddr' (updateStorage (EVM.SStore addr e'') contract, cid) writeMap, [])]
    TByteStr -> error "Bytestrings not supported"
    TInteger _ _ -> do
        e' <- toExpr readMap callenv e
        let prevValue = readStorage addr contract
        let e'' = storedValue e' prevValue offset size
        pure [(M.insert caddr' (updateStorage (EVM.SStore addr e'') contract, cid) writeMap, [])]
    TBoolean -> do
        e' <- toExpr readMap callenv e
        let prevValue = readStorage addr contract
        let e'' = storedValue e' prevValue offset size
        pure [(M.insert caddr' (updateStorage (EVM.SStore addr e'') contract, cid) writeMap, [])]
    TAddress -> do
        e' <- toExpr readMap callenv e
        let prevValue = readStorage addr contract
        let e'' = storedValue e' prevValue offset size
        pure [(M.insert caddr' (updateStorage (EVM.SStore addr e'') contract, cid) writeMap, [])]
    TMapping _ _ -> do
        let expansion = expandMappingUpdate tref e
        foldM (\wms (tr,te) -> concatMapM (\(wm,cs) -> (fmap $ second (cs ++)) <$> writeToRef readMap wm callenv tr te) wms) [(writeMap, [])] expansion
    TArray _ _ -> error "arrays TODO"
    TStruct _ -> error "structs TODO"
    TUnboundedInt -> error "Internal error: Unbounded Integer after typechecking"
-- TODO test with out of bounds assignments
  where
    storedValue :: EVM.Expr EVM.EWord -> EVM.Expr EVM.EWord -> EVM.Expr EVM.EWord -> Int -> EVM.Expr EVM.EWord
    storedValue new prev offset size =
        let offsetBits = EVM.Mul (EVM.Lit 8) offset in
        let maxVal = EVM.Lit $ (2 ^ (8 * size)) - 1 in
        let mask = EVM.Xor (EVM.SHL offsetBits maxVal) (EVM.Lit MAX_UINT) in
        let newShifted = EVM.SHL offsetBits new in
        EVM.Or newShifted (EVM.And prev mask)

    updateStorage :: (EVM.Expr EVM.Storage -> EVM.Expr EVM.Storage) -> EVM.Expr EVM.EContract -> EVM.Expr EVM.EContract
    updateStorage updfun (EVM.C code storage tstorage bal nonce) = EVM.C code (updfun storage) tstorage bal nonce
    updateStorage _ (EVM.GVar _) = error "Internal error: contract cannot be a global variable"

    readStorage :: EVM.Expr EVM.EWord -> EVM.Expr EVM.EContract -> EVM.Expr EVM.EWord
    readStorage addr (EVM.C _ storage _ _ _) = EVM.SLoad addr storage
    readStorage _ (EVM.GVar _) = error "Internal error: contract cannot be a global variable"

    updateNonce :: EVM.Expr EVM.EContract -> EVM.Expr EVM.EContract
    updateNonce (EVM.C code storage tstorage bal (Just n)) = EVM.C code storage tstorage bal (Just (n + 1))
    updateNonce c@(EVM.C _ _ _ _ Nothing) = c
    updateNonce (EVM.GVar _) = error "Internal error: contract cannot be a global variable"

    isCreate (Create _ _ _ _) = True
    isCreate (Address _ _ (Create _ _ _ _)) = True
    isCreate _ = False

createCastedContract :: Monad m => ContractMap -> ContractMap -> CallEnv -> EVM.Expr EVM.EAddr -> Exp AInteger -> ActT m [(ContractMap, [EVM.Prop])]
createCastedContract readMap writeMap callenv freshAddr (Address _ _ (Create pn cid args b)) =
 createContract readMap writeMap callenv freshAddr (Create pn cid args b)
createCastedContract _ _ _ _ _ = error "Internal error: constructor call expected"

createContract :: Monad m => ContractMap -> ContractMap -> CallEnv -> EVM.Expr EVM.EAddr -> Exp AContract -> ActT m [(ContractMap, [EVM.Prop])]
createContract readMap writeMap callenv freshAddr (Create _ cid args _) = do
  codemap <- getCodemap
  case M.lookup cid codemap of
    -- TODO: handle multiple cases
    Just (Contract (Constructor _ _ _ _ [] _ _) _, _, _) ->
      error $ "Internal error: Contract " <> cid <> " has no cases from which to form map\n" <> show codemap
    Just (Contract (Constructor _ iface _ _ cases _ _) _, _, bytecode) -> do
      --callenv' <- makeCallEnv readMap callenv iface args
      --applyUpdates readMap (M.insert freshAddr (contract, cid) writeMap) callenv' upds
      concatMapM applyCase cases
      where
        applyCase :: Monad m => Ccase -> ActT m [(ContractMap, [EVM.Prop])]
        applyCase (Case _ caseCond upds) = do
          callenv' <- makeCallEnv readMap callenv iface args
          caseCond' <- toProp readMap callenv' caseCond
          (fmap $ second (caseCond' : )) <$> applyUpdates readMap (M.insert freshAddr (contract, cid) writeMap) callenv' upds

        contract = EVM.C { EVM.code  = EVM.RuntimeCode (EVM.ConcreteRuntimeCode bytecode)
                           , EVM.storage = EVM.ConcreteStore mempty
                           , EVM.tStorage = EVM.ConcreteStore mempty
                           , EVM.balance = EVM.Lit 0
                           , EVM.nonce = Just 1
                           }
    Nothing -> error "Internal error: constructor not found"
createContract _ _ _ _ _ = error "Internal error: constructor call expected"
-- TODO typing needs to semantically checks for preconditions

type CallEnv = (M.Map Id (EVM.Expr EVM.EWord))

emptyEnv :: CallEnv
emptyEnv = M.empty

-- | Create constructor call environment
makeCallEnv :: Monad m => ContractMap -> CallEnv -> Interface -> [TypedExp] -> ActT m CallEnv
makeCallEnv cmap callenv (Interface _ decls) args = do
  lst <- zipWithM (\(Arg _ x) texp -> do
    wexpr <- typedExpToWord cmap callenv texp
    pure (x, wexpr)) decls args
  pure $ M.fromList lst

returnsToExpr :: Monad m => ContractMap -> CallEnv -> Maybe TypedExp -> ActT m (EVM.Expr EVM.Buf)
returnsToExpr _ _ Nothing = pure $ EVM.ConcreteBuf ""
returnsToExpr cmap callenv (Just r) = typedExpToBuf cmap callenv r

wordToBuf :: EVM.Expr EVM.EWord -> EVM.Expr EVM.Buf
wordToBuf w = EVM.WriteWord (EVM.Lit 0) w (EVM.ConcreteBuf "")

wordToProp :: EVM.Expr EVM.EWord -> EVM.Prop
wordToProp w = EVM.PNeg (EVM.PEq w (EVM.Lit 0))

typedExpToBuf :: Monad m => ContractMap -> CallEnv -> TypedExp -> ActT m (EVM.Expr EVM.Buf)
typedExpToBuf cmap callenv expr =
  case expr of
    TExp styp e -> expToBuf cmap callenv styp e

typedExpToWord :: Monad m => ContractMap -> CallEnv -> TypedExp -> ActT m (EVM.Expr EVM.EWord)
typedExpToWord cmap callenv te = do
    case te of
        TExp vtyp e -> case vtyp of
            TInteger _ _ -> toExpr cmap callenv e
            TUnboundedInt -> toExpr cmap callenv e
            TContract _ -> toExpr cmap callenv e -- TODO: is this correct?
            TAddress -> toExpr cmap callenv e
            TBoolean -> toExpr cmap callenv e
            TByteStr -> error "Bytestring in unexpected position"
            TArray _ _ -> error "TODO arrays"
            TStruct _ -> error "TODO structs"
            TMapping _ _ -> error "TODO Mappings" -- TODO

expToBuf :: Monad m => forall a. ContractMap -> CallEnv -> TValueType a -> Exp a  -> ActT m (EVM.Expr EVM.Buf)
expToBuf cmap callenv vtyp e = do
  case vtyp of
    (TInteger _ _) -> do
      e' <- toExpr cmap callenv e
      pure $ EVM.WriteWord (EVM.Lit 0) e' (EVM.ConcreteBuf "")
    (TContract _) -> do  -- TODO: is this correct?
      e' <- toExpr cmap callenv e
      pure $ EVM.WriteWord (EVM.Lit 0) e' (EVM.ConcreteBuf "")
    TAddress -> do
      e' <- toExpr cmap callenv e
      pure $ EVM.WriteWord (EVM.Lit 0) e' (EVM.ConcreteBuf "")
    TBoolean -> do
      e' <- toExpr cmap callenv e
      pure $ EVM.WriteWord (EVM.Lit 0) (EVM.IsZero $ EVM.IsZero e') (EVM.ConcreteBuf "")
    TByteStr -> toExpr cmap callenv e
    TArray _ _ -> error "TODO arrays"
    TStruct _ -> error "TODO structs"
    TMapping _ _ -> error "TODO mappings" -- TODO
    TUnboundedInt -> error "Internal error: Unbounded Integer after typechecking"

-- | Get the slot and the offset of a storage variable in storage
getPosition :: Layout -> Id -> Id -> (Int, Int, Int, LayoutMode)
getPosition layout cid name =
  case M.lookup cid layout of
    Just (lm, m) -> case M.lookup name m of
      Just (p1,p2,p3) -> (p1,p2,p3,lm)
      Nothing -> error $ "Internal error: invalid variable name: " <> show name
    Nothing -> error "Internal error: invalid contract name"

-- | For the given storage reference, it returs the memory slot, the offset
-- of the value within the slot, and the size of the value.
refOffset :: Monad m => ContractMap -> CallEnv -> Ref k -> ActT m (EVM.Expr EVM.EWord, EVM.Expr EVM.EWord, Int, LayoutMode)
refOffset _ _ (CVar _ _ _) = error "Internal error: ill-typed entry"
refOffset _ _ (SVar _ _ cid name) = do
  layout <- getLayout
  let (slot, off, size, layoutMode) = getPosition layout cid name
  pure (EVM.Lit (fromIntegral slot), EVM.Lit $ fromIntegral off, size, layoutMode)
refOffset cmap callenv (RMapIdx _ (TRef (TMapping _ t) _ ref) ix) = do
  (slot, _, _, layoutMode) <- refOffset cmap callenv ref
  buf <- typedExpToBuf cmap callenv ix
  let concatenation = case layoutMode of
        SolidityLayout -> buf <> (wordToBuf slot)
        VyperLayout -> (wordToBuf slot) <> buf
  let addr = (EVM.keccak concatenation)
  let size =  case layoutMode of
        SolidityLayout -> sizeOfValue t
        VyperLayout -> 32
  pure (addr, EVM.Lit 0, size, layoutMode)
refOffset _ _ (RField _ _ cid name) = do
  layout <- getLayout
  let (slot, off, size, layoutMode) = getPosition layout cid name
  pure (EVM.Lit (fromIntegral slot), EVM.Lit $ fromIntegral off, size, layoutMode)
refOffset _ _ (RArrIdx _ _ _ _) = error "TODO"
refOffset _ _ (RMapIdx _ (TRef _ _ _) _) = error "Internal error: Map Index into non-map reference"


-- | Get the address of the contract whoose storage contrains the given
-- reference
baseAddr :: Monad m => ContractMap -> CallEnv -> Ref k -> ActT m (EVM.Expr EVM.EAddr)
baseAddr _ _ (SVar _ _ _ _) = getCaddr
baseAddr _ _ (CVar _ _ _) = error "Internal error: ill-typed entry"
baseAddr cmap callenv (RField _ ref _ _) = do
  expr <- refToExp cmap callenv ref
  case simplify expr of
    EVM.WAddr symaddr -> pure symaddr
    e -> error $ "Internal error: did not find a symbolic address: " <> show e
baseAddr cmap callenv (RMapIdx _ (TRef _ _ ref) _) = baseAddr cmap callenv ref
baseAddr cmap callenv (RArrIdx _ ref _ _) = baseAddr cmap callenv ref


ethEnvToWord :: Monad m => EthEnv -> ActT m (EVM.Expr EVM.EWord)
ethEnvToWord Callvalue = pure EVM.TxValue
ethEnvToWord Caller = do
  c <- getCaller
  pure $ EVM.WAddr c
ethEnvToWord Origin = pure $ EVM.WAddr (EVM.SymAddr "origin") -- Why not: pure $ EVM.Origin
ethEnvToWord This = do
  c <- getCaddr
  pure $ EVM.WAddr c

ethEnvToBuf :: EthEnv -> EVM.Expr EVM.Buf
ethEnvToBuf _ = error "Internal error: there are no bytestring environment values"


toProp :: Monad m => ContractMap -> CallEnv -> Exp ABoolean -> ActT m EVM.Prop
toProp cmap callenv = \case
  (And _ e1 e2) -> pop2 EVM.PAnd e1 e2
  (Or _ e1 e2) -> pop2 EVM.POr e1 e2
  (Impl _ e1 e2) -> pop2 EVM.PImpl e1 e2
  (Neg _ e1) -> do
    e1' <- toProp cmap callenv e1
    pure $ EVM.PNeg e1'
  (Act.LT _ e1 e2) -> op2 EVM.PLT e1 e2
  (LEQ _ e1 e2) -> op2 EVM.PLEq e1 e2
  (GEQ _ e1 e2) -> op2 EVM.PGEq e1 e2
  (Act.GT _ e1 e2) -> op2 EVM.PGT e1 e2
  (LitBool _ b) -> pure $ EVM.PBool b
  (Eq _ (TInteger _ _) e1 e2) -> op2 EVM.PEq e1 e2
  (Eq _ (TContract _) e1 e2) -> op2 EVM.PEq e1 e2
  (Eq _ TAddress e1 e2) -> op2 EVM.PEq e1 e2
  (Eq _ TBoolean e1 e2) -> op2 EVM.PEq e1 e2
  (Eq _ _ _ _) -> error "unsupported"
  (NEq _ (TInteger _ _) e1 e2) -> do
    e <- op2 EVM.PEq e1 e2
    pure $ EVM.PNeg e
  (NEq _ (TContract _) e1 e2) -> do
    e <- op2 EVM.PEq e1 e2
    pure $ EVM.PNeg e
  (NEq _ TAddress e1 e2) -> do
    e <- op2 EVM.PEq e1 e2
    pure $ EVM.PNeg e
  (NEq _ TBoolean e1 e2) -> do
    e <- op2 EVM.PEq e1 e2
    pure $ EVM.PNeg e
  (NEq _ _ _ _) -> error "unsupported"
  (ITE _ _ _ _) -> error "Internal error: expecting flat expression"
  (VarRef _ _ ref) -> EVM.PEq (EVM.Lit 0) <$> EVM.IsZero <$> refToExp cmap callenv ref
  (InRange _ t e) -> toProp cmap callenv (inRange t e)
  where
    op2 :: Monad m => forall a b. (EVM.Expr (ExprType b) -> EVM.Expr (ExprType b) -> a) -> Exp b -> Exp b -> ActT m a
    op2 op e1 e2 = do
      e1' <- toExpr cmap callenv e1
      e2' <- toExpr cmap callenv e2
      pure $ op e1' e2'

    pop2 :: Monad m => forall a. (EVM.Prop -> EVM.Prop -> a) -> Exp ABoolean -> Exp ABoolean -> ActT m a
    pop2 op e1 e2 = do
      e1' <- toProp cmap callenv e1
      e2' <- toProp cmap callenv e2
      pure $ op e1' e2'

pattern MAX_UINT :: EVM.W256
pattern MAX_UINT = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

-- TODO: this belongs to HEVM
stripMods :: EVM.Expr a -> EVM.Expr a
stripMods = mapExpr go
  where
    go :: EVM.Expr a -> EVM.Expr a
    go (EVM.Mod a (EVM.Lit MAX_UINT)) = a
    go a = a

toExpr :: forall a m. Monad m => ContractMap -> CallEnv -> TA.Exp a Timed -> ActT m (EVM.Expr (ExprType a))
toExpr cmap callenv =  fmap stripMods . go
  where
    go :: Monad m => Exp a -> ActT m (EVM.Expr (ExprType a))
    go = \case
      -- booleans
      (And _ e1 e2) -> op2 EVM.And e1 e2
      (Or _ e1 e2) -> op2 EVM.Or e1 e2
      (Impl _ e1 e2) -> op2 (EVM.Or . EVM.Not) e1 e2
      (Neg _ e1) -> do
        e1' <- toExpr cmap callenv e1
        pure $ EVM.IsZero e1' -- XXX why EVM.Not fails here?
      (Act.LT _ e1 e2) -> op2 EVM.LT e1 e2
      (LEQ _ e1 e2) -> op2 EVM.LEq e1 e2
      (GEQ _ e1 e2) -> op2 EVM.GEq e1 e2
      (Act.GT _ e1 e2) -> op2 EVM.GT e1 e2
      (LitBool _ b) -> pure $ EVM.Lit (fromIntegral $ fromEnum b)
      -- integers
      (Add _ e1 e2) -> op2 EVM.Add e1 e2
      (Sub _ e1 e2) -> op2 EVM.Sub e1 e2
      (Mul _ e1 e2) -> op2 EVM.Mul e1 e2
      (Div _ e1 e2) -> op2 EVM.Div e1 e2
      (Mod _ e1 e2) -> op2 EVM.Mod e1 e2 -- which mod?
      (Exp _ e1 e2) -> op2 EVM.Exp e1 e2
      (LitInt _ n) -> pure $ EVM.Lit (fromIntegral n)
      (IntEnv _ env) -> ethEnvToWord env
      -- bounds
      (IntMin _ n) -> pure $ EVM.Lit (fromIntegral $ intmin n)
      (IntMax _ n) -> pure $ EVM.Lit (fromIntegral $ intmax n)
      (UIntMin _ n) -> pure $ EVM.Lit (fromIntegral $ uintmin n)
      (UIntMax _ n) -> pure $ EVM.Lit (fromIntegral $ uintmax n)
      (InRange _ t e) -> toExpr cmap callenv (inRange t e)
      -- bytestrings
      (Cat _ _ _) -> error "TODO"
      (Slice _ _ _ _) -> error "TODO"
      -- EVM.CopySlice (toExpr start) (EVM.Lit 0) -- src and dst offset
      -- (EVM.Add (EVM.Sub (toExp end) (toExpr start)) (EVM.Lit 0)) -- size
      -- (toExpr bs) (EVM.ConcreteBuf "") -- src and dst
      (ByStr _ str) -> pure $  EVM.ConcreteBuf (B8.pack str)
      (ByLit _ bs) -> pure $ EVM.ConcreteBuf bs
      (ByEnv _ env) -> pure $ ethEnvToBuf env
      -- contracts
      (Create _ _ _ _) -> error "internal error: Create calls not supported in this context"
      -- polymorphic
      (Eq _ (TInteger _ _) e1 e2) -> op2 EVM.Eq e1 e2
      (Eq _ (TContract _) e1 e2) -> op2 EVM.Eq e1 e2
      (Eq _ TBoolean e1 e2) -> op2 EVM.Eq e1 e2
      (Eq _ TAddress e1 e2) -> op2 EVM.Eq e1 e2
      (Eq _ _ _ _) -> error "unsupported"

      (NEq _ (TInteger _ _) e1 e2) -> do
        e <- op2 EVM.Eq e1 e2
        pure $ EVM.Not e
      (NEq _ (TContract _) e1 e2) -> do
        e <- op2 EVM.Eq e1 e2
        pure $ EVM.Not e
      (NEq _ TBoolean e1 e2) -> do
        e <- op2 EVM.Eq e1 e2
        pure $ EVM.Not e
      (NEq _ TAddress e1 e2) -> do
        e <- op2 EVM.Eq e1 e2
        pure $ EVM.Not e
      (NEq _ _ _ _) -> error "unsupported"

      (VarRef _ (TInteger _ _) ref) -> refToExp cmap callenv ref --TODO: more cases?
      (VarRef _ TBoolean ref) -> refToExp cmap callenv ref
      (VarRef _ TAddress ref) -> refToExp cmap callenv ref
      (VarRef _ (TContract _) ref) -> refToExp cmap callenv ref

      e@(ITE _ _ _ _) -> error $ "Internal error: expecting flat expression. got: " <> show e

      (Address _ _ e') -> toExpr cmap callenv e'
      e ->  error $ "TODO: " <> show e

    op2 :: Monad m => forall b c. (EVM.Expr (ExprType c) -> EVM.Expr (ExprType c) -> b) -> Exp c -> Exp c -> ActT m b
    op2 op e1 e2 = do
      e1' <- toExpr cmap callenv e1
      e2' <- toExpr cmap callenv e2
      pure $ op e1' e2'


-- | Extract a value from a slot using its offset and size
extractValue ::  EVM.Expr EVM.EWord -> EVM.Expr EVM.EWord -> Int -> EVM.Expr EVM.EWord
extractValue slot offset size =
    let mask = EVM.Lit $ 2 ^ (8 * size) - 1 in
    let bits = EVM.Mul offset (EVM.Lit 8) in
    EVM.And (EVM.SHR bits slot) mask


refToExp :: forall m k. Monad m => ContractMap -> CallEnv -> Ref k -> ActT m (EVM.Expr EVM.EWord)
-- calldata variable
refToExp _ callenv (CVar _ typ x) = case M.lookup x callenv of
    Just e -> pure e
    Nothing -> pure $ fromCalldataFramgment $ symAbiArg (T.pack x) (argToAbiType typ)

  where
    fromCalldataFramgment :: CalldataFragment -> EVM.Expr EVM.EWord
    fromCalldataFramgment (St _ word) = word
    fromCalldataFramgment _ = error "Internal error: only static types are supported"

refToExp cmap callenv r = do
  caddr <- baseAddr cmap callenv r
  (slot, offset, size, _) <- refOffset cmap callenv r
  let word = accessStorage cmap slot caddr
  pure $ extractValue word offset size

accessStorage :: ContractMap -> EVM.Expr EVM.EWord -> EVM.Expr EVM.EAddr -> EVM.Expr EVM.EWord
accessStorage cmap slot addr = case M.lookup addr cmap of
  Just (EVM.C _ storage _ _ _, _) ->
    EVM.SLoad slot storage
  Just (EVM.GVar _, _) -> error "Internal error: contract cannot be a global variable"
  Nothing -> error $ "Internal error: contract not found " <> show addr <> "\nmap:" <> show cmap


inRange :: TValueType AInteger -> Exp AInteger -> Exp ABoolean
-- if the type has the type of machine word then check per operation
inRange (TInteger 256 Unsigned) e = checkOp e
inRange (TInteger 256 Signed) _ = error "TODO signed integers"
-- otherwise insert range bounds
inRange t e = bound t e


checkOp :: Exp AInteger -> Exp ABoolean
checkOp (LitInt _ i) = LitBool nowhere $ i <= (fromIntegral (maxBound :: Word256))
checkOp (VarRef _ _ _)  = LitBool nowhere True
checkOp e@(Add _ e1 _) = LEQ nowhere e1 e -- check for addition overflow
checkOp e@(Sub _ e1 _) = LEQ nowhere e e1
checkOp (Mul _ e1 e2) = Or nowhere (Eq nowhere (TInteger 256 Unsigned) e1 (LitInt nowhere 0))
                          (Impl nowhere (NEq nowhere (TInteger 256 Unsigned) e1 (LitInt nowhere 0))
                            (Eq nowhere (TInteger 256 Unsigned) e2 (Div nowhere (Mul nowhere e1 e2) e1)))
checkOp (Div _ _ _) = LitBool nowhere True
checkOp (Mod _ _ _) = LitBool nowhere True
checkOp (Address _ _ _) = LitBool nowhere True
checkOp (Exp _ _ _) = error "TODO check for exponentiation overflow"
checkOp (IntMin _ _)  = error "Internal error: invalid in range expression"
checkOp (IntMax _ _)  = error "Internal error: invalid in range expression"
checkOp (UIntMin _ _) = error "Internal error: invalid in range expression"
checkOp (UIntMax _ _) = error "Internal error: invalid in range expression"
checkOp (ITE _ _ _ _) = error "Internal error: invalid in range expression"
checkOp (IntEnv _ _) = error "Internal error: invalid in range expression"


-- Equivalence checking

-- | Wrapper for the equivalenceCheck function of hevm
checkEquiv :: App m => SolverGroup -> [EVM.Expr EVM.End] -> [EVM.Expr EVM.End] -> m [EquivResult]
checkEquiv solvers l1 l2 = do
  EqIssues res _ <- equivalenceCheck' solvers l1 l2 False
  pure $ fmap (toEquivRes . fst) res
  where
    toEquivRes :: EVM.EquivResult -> EquivResult
    toEquivRes (EVM.Cex cex) = EVM.Cex ("\x1b[1mThe following input results in different behaviours\x1b[m", cex)
    toEquivRes EVM.Qed = EVM.Qed
    toEquivRes (EVM.Unknown s) = EVM.Unknown s
    toEquivRes (EVM.Error b) = EVM.Error b


-- | Create the initial contract state before analysing a contract
-- It checks (using SMT) that each symbolic address present in the intial map is distinct.
-- Assumes that all calldata variables have unique names (TODO alpha renaming)
getInitContractState :: App m => SolverGroup -> Id -> Interface -> [Exp ABoolean] -> ContractMap -> ActT m (ContractMap, Error String ())
getInitContractState solvers cname iface preconds cmap = do
  let casts = castsFromIFace iface
  let casts' = groupBy (\x y -> fst x == fst y) casts
  (cmaps, checks) <- mapAndUnzipM getContractState (fmap nub casts')

  let finalmap = M.unions (cmap:cmaps)

  check <- checkAliasing finalmap cmaps
  pure (finalmap, check <* sequenceA_ checks <* checkUniqueAddr (cmap:cmaps))

  where
    castsFromIFace :: Interface -> [(Id, Id)]
    castsFromIFace (Interface _ decls) = mapMaybe castingDecl decls
      where
      castingDecl (Arg (ContractArg _ cid) name) = Just (name, cid)
      castingDecl _ = Nothing

    getContractState :: App m => [(Id, Id)] -> ActT m (ContractMap, Error String ())
    getContractState [(x, cid)] = do
      let addr = EVM.SymAddr $ T.pack x
      codemap <- getCodemap
      case M.lookup cid codemap of
        -- TODO: handle multiple cases
        Just (Contract (Constructor cname' iface' _ preconds' ((Case _ _ upds):_) _ _) _, _, bytecode) -> do
          (icmap, check) <- getInitContractState solvers cname' iface' preconds' M.empty
          let contract = EVM.C { EVM.code  = EVM.RuntimeCode (EVM.ConcreteRuntimeCode bytecode)
                               , EVM.storage = EVM.ConcreteStore mempty
                               , EVM.tStorage = EVM.ConcreteStore mempty
                               , EVM.balance = EVM.Lit 0
                               , EVM.nonce = Just 1
                               }
          let icmap' = M.insert addr (contract, cid) icmap
          cmap' <- localCaddr addr $ applyUpdates icmap' icmap' emptyEnv upds
          pure (abstractCmap addr (fst $ head cmap'), check)
        Just (Contract (Constructor _ _ _ _ [] _ _) _, _, _) ->
          error $ "Internal error: Contract " <> cid <> " has no cases from which to form init map\n" <> show codemap
        Nothing -> error $ "Internal error: Contract " <> cid <> " not found\n" <> show codemap
    getContractState [] = error "Internal error: Cast cannot be empty"
    getContractState _ = error "Error: Cannot have different casts to the same address"

    checkAliasing :: App m => ContractMap -> [ContractMap] -> ActT m (Error String ())
    checkAliasing cmap' cmaps = do
      let allkeys = M.foldrWithKey (\k (_, cid) l -> (k, cid):l) [] <$> cmaps
      -- gather all tuples that must be distinct
      let allpairs = concatMap (\(l1, l2) -> (,) <$> l1 <*> l2) $ comb allkeys
      -- gather all tuples that we know are distinct
      fresh <- getFresh
      let distpairs = (\(a1, a2) -> neqProp (makeSymAddr a1) (makeSymAddr a2)) <$> comb [1..fresh]
      let dquery = EVM.por $ (\((a1, c1),(a2, c2)) ->
                                if c1 == c2 then EVM.PEq (EVM.WAddr a1) (EVM.WAddr a2) else EVM.PBool False) <$> allpairs
      preconds' <- mapM (toProp cmap' emptyEnv) preconds
      lift $ checkQueries (dquery:distpairs <> preconds')

    checkQueries :: App m => [EVM.Prop] -> m (Error String ())
    checkQueries queries = do
      conf <- readConfig
      res <- liftIO $ checkSat solvers Nothing (assertProps conf queries)
      checkResult (makeCalldata cname iface) Nothing [toVRes msg res]

    makeSymAddr n = EVM.WAddr (EVM.SymAddr $ "freshSymAddr" <> (T.pack $ show n))
    neqProp a1 a2 = EVM.PNeg (EVM.PEq a1 a2)

    msg = "\x1b[1mThe following addresses cannot be proved distinct:\x1b[m"

    -- currently we check that all symbolic addresses are globaly unique, and fail otherwise
    -- (this is required for aliasing check to be sound when merging graphs
    -- In the future, we should implement an internal renaming of variables to ensure global
    -- uniqueness of symbolic addresses.)

    checkUniqueAddr :: [ContractMap] -> Error String ()
    checkUniqueAddr cmaps =
      let pairs = comb cmaps in
      assert (nowhere, "Names of symbolic adresses must be unique") (foldl (\b (c1, c2) -> S.disjoint (M.keysSet c1) (M.keysSet c2) && b) True pairs)

comb :: Show a => [a] -> [(a,a)]
comb xs = [(x,y) | (x:ys) <- tails xs, y <- ys]

checkConstructors :: App m => SolverGroup -> ByteString -> ByteString -> Contract -> ActT m (Error String ContractMap)
checkConstructors solvers initcode runtimecode (Contract ctor@(Constructor cname iface _ preconds _ _ _)  _) = do
  -- Construct the initial contract state
  (actinitmap, checks) <- getInitContractState solvers cname iface preconds M.empty
  let hevminitmap = translateCmap actinitmap
  -- Translate Act constructor to Expr
  fresh <- getFresh
  (actbehvs, calldata, sig, bounds) <- translateConstructor runtimecode ctor actinitmap
  let (behvs', fcmaps) = unzip actbehvs
    -- Symbolically execute bytecode
    -- TODO check if contrainsts about preexistsing fresh symbolic addresses are necessary
  solbehvs <- lift $ removeFails <$> getInitcodeBranches solvers initcode hevminitmap calldata bounds fresh

  --traceM $ "sol: " ++ showBehvs solbehvs
  --traceM $ "act: " ++ showBehvs behvs'

  -- Check equivalence
  lift $ showMsg "\x1b[1mChecking if constructor results are equivalent.\x1b[m"
  res1 <- lift $ checkResult calldata (Just sig) =<< checkEquiv solvers solbehvs behvs'
  lift $ showMsg "\x1b[1mChecking if constructor input spaces are the same.\x1b[m"
  res2 <- lift $ checkResult calldata (Just sig) =<< checkInputSpaces solvers solbehvs behvs'
  pure $ traverse_ (checkStoreIsomorphism (head fcmaps)) (tail fcmaps) *> checks *> res1 *> res2 *> Success (head fcmaps)
  where
    removeFails branches = filter isSuccess branches


checkBehaviours :: forall m. App m => SolverGroup -> Contract -> ContractMap -> ActT m (Error String ())
checkBehaviours solvers (Contract _ behvs) actstorage = do
  let hevmstorage = translateCmap actstorage
  fresh <- getFresh
  actbehvs <- translateBehvs actstorage behvs
  (fmap $ concatError def) $ forM actbehvs $ \(name,actbehv,calldata,sig,bounds) -> do
    let (behvs', fcmaps) = unzip actbehv

    solbehvs <- lift $ removeFails <$> getRuntimeBranches solvers hevmstorage calldata bounds fresh

    lift $ showMsg $ "\x1b[1mChecking behavior \x1b[4m" <> name <> "\x1b[m of Act\x1b[m"
    -- equivalence check
    lift $ showMsg "\x1b[1mChecking if behaviour is matched by EVM\x1b[m"
    res1 <- lift $ checkResult calldata (Just sig) =<< checkEquiv solvers solbehvs behvs'
    -- input space exhaustiveness check
    lift $ showMsg "\x1b[1mChecking if the input spaces are the same\x1b[m"
    res2 <- lift $ checkResult calldata (Just sig) =<< checkInputSpaces solvers solbehvs behvs'
    pure $ traverse_ (checkStoreIsomorphism actstorage) fcmaps *> res1 *> res2

  where
    removeFails branches = filter isSuccess branches
    def = Success ()


translateCmap :: ContractMap -> [(EVM.Expr EVM.EAddr, EVM.Contract)]
translateCmap cmap = (\(addr, (c, _)) -> (addr, toContract c)) <$> M.toList cmap
  where
    toContract :: EVM.Expr EVM.EContract -> EVM.Contract
    toContract (EVM.C code storage tstorage balance nonce) = EVM.Contract
      { EVM.code        = code
      , EVM.storage     = storage
      , EVM.tStorage    = tstorage
      , EVM.origStorage = storage
      , EVM.balance     = balance
      , EVM.nonce       = nonce
      , EVM.codehash    = EVM.hashcode code
      , EVM.opIxMap     = EVM.mkOpIxMap code
      , EVM.codeOps     = EVM.mkCodeOps code
      , EVM.external    = False
      }
    toContract (EVM.GVar _) = error "Internal error: contract cannot be gvar"


abstractCmap :: EVM.Expr EVM.EAddr -> ContractMap -> ContractMap
abstractCmap this cmap =
  pruneContractState this $ M.mapWithKey makeContract cmap
  where
    traverseStorage ::  EVM.Expr EVM.EAddr -> EVM.Expr EVM.Storage -> EVM.Expr EVM.Storage
    traverseStorage addr (EVM.SStore offset (EVM.WAddr symaddr) storage) =
      if M.member symaddr cmap then
        EVM.SStore offset (EVM.WAddr symaddr) (traverseStorage addr storage)
      else traverseStorage addr storage
    traverseStorage addr (EVM.SStore _ _ storage) = traverseStorage addr storage
    traverseStorage addr (EVM.ConcreteStore _) = EVM.AbstractStore addr Nothing
    traverseStorage _ s@(EVM.AbstractStore {}) = s
    traverseStorage _ _ = error "Internal error: unexpected storage shape"

    makeContract :: EVM.Expr EVM.EAddr -> (EVM.Expr EVM.EContract, Id) -> (EVM.Expr EVM.EContract, Id)
    makeContract addr (EVM.C code storage tstorage _ _, cid) =
      (EVM.C code (simplify (traverseStorage addr (simplify storage))) tstorage (EVM.Balance addr) (Just 0), cid)
    makeContract _ (EVM.GVar _, _) = error "Internal error: contract cannot be gvar"

-- | Remove unreachable addresses from a contract map
-- Assumes:
-- 1. all stores are to concrete addresses (this is OK, since this is the abstracted map
--    containing only the slots that point to contracts)
-- 2. The storage map is simplfied. This means that all contract addresses stored as values
--    are of the form (EVM.WAddr symaddr)
pruneContractState :: EVM.Expr EVM.EAddr -> ContractMap -> ContractMap
pruneContractState entryaddr cmap =
  let reach = reachable entryaddr cmap in
  M.filterWithKey (\k _ -> elem k reach) cmap

  where
    -- Find reachable addresses from given address
    reachable :: EVM.Expr EVM.EAddr -> ContractMap -> [EVM.Expr EVM.EAddr]
    reachable addr cmap' = nub $ go addr []
      where
        -- Note: there state is a tree, no need to mark visisted
        go :: EVM.Expr EVM.EAddr -> [EVM.Expr EVM.EAddr] -> [EVM.Expr EVM.EAddr]
        go addr' acc =
          case M.lookup addr' cmap' of
            Just (EVM.C _ storage _ _ _, _) ->
              let addrs = snd <$> getAddrs storage in
              foldr go (addr':acc) addrs
            Just (EVM.GVar _, _) -> error "Internal error: contract cannot be gvar"
            Nothing -> error "Internal error: contract not found"


-- | Check if two contract maps are isomorphic.
-- Perform a breadth first traversal and try to find a bijection between the addresses of the two stores
-- Note that this problem is not as difficult as graph isomorphism since edges are labeled.
-- Assumes that the stores are abstracted, pruned, and simplified.
-- All writes are to a unique concrete slot and the value is a symbolic address.
checkStoreIsomorphism :: ContractMap -> ContractMap -> Error String ()
checkStoreIsomorphism cmap1 cmap2 =
    bfs [(idOfAddr initAddr, idOfAddr initAddr)] [] M.empty M.empty
  where
    -- tries to find a bijective renaming between the addresses of the two maps
    bfs :: [(T.Text, T.Text)]                         -- Queue of the addresses we are exploring (dequeue)
        -> [(T.Text, T.Text)]                         -- Queue of the addresses we are exploring (enueue)
        -> M.Map T.Text T.Text -> M.Map T.Text T.Text -- Two renamings keeping track of the address bijection
        -> Error String ()
    bfs [] [] _ _  = pure ()
    bfs [] q2 m1 m2 = bfs (reverse q2) [] m1 m2
    bfs ((addr1, addr2):q1) q2  map1 map2 =
      case (M.lookup (EVM.SymAddr addr1) cmap1, M.lookup (EVM.SymAddr addr2) cmap2) of
        (Just (EVM.C _ storage1 _ _ _, _), Just (EVM.C _ storage2 _ _ _, _)) ->
          let addrs1 = sortOn fst $ getAddrs storage1 in
          let addrs2 = sortOn fst $ getAddrs storage2 in
          visit addrs1 addrs2 map1 map2 q2 `bindValidation` (\(renaming1, renaming2, q2') ->
          bfs q1 q2' renaming1 renaming2)
        (_, _) -> error "Internal error: contract not found in map"

    -- assumes that slots are unique because of simplifcation
    visit :: [(Int, EVM.Expr EVM.EAddr)] -> [(Int, EVM.Expr EVM.EAddr)]
          -> M.Map T.Text T.Text -> M.Map T.Text T.Text
          -> [(T.Text, T.Text)]
          -> Error String (M.Map T.Text T.Text, M.Map T.Text T.Text, [(T.Text, T.Text)])
    visit [] [] map1 map2 discovered = pure (map1, map2, discovered)
    visit ((s1, EVM.SymAddr a1):addrs1) ((s2, EVM.SymAddr a2):addrs2) map1 map2 discovered | s1 == s2 =
      case (M.lookup a1 map1, M.lookup a2 map2) of
        (Just a2', Just a1') ->
          if a2 == a2' && a1 == a1' then visit addrs1 addrs2 map1 map2 discovered
          else throw (nowhere, "The shape of the resulting map is not preserved.")
        (Nothing, Nothing) -> visit addrs1 addrs2 (M.insert a1 a2 map1) (M.insert a2 a1 map2) ((a1, a2): discovered)
        (_, _) -> throw (nowhere, "The shape of the resulting map is not preserved.")
    visit _ _ _ _  _ = throw (nowhere, "The shape of the resulting map is not preserved.")

-- Find addresses mentioned in storage
getAddrs :: EVM.Expr EVM.Storage -> [(Int, EVM.Expr EVM.EAddr)]
getAddrs (EVM.SStore (EVM.Lit n) (EVM.WAddr symaddr) storage) = (fromIntegral n, symaddr) : getAddrs storage
getAddrs (EVM.SStore _ _ _) = error "Internal error: unexpected storage shape"
getAddrs (EVM.ConcreteStore _) = error "Internal error: unexpected storage shape"
getAddrs (EVM.AbstractStore {}) = []
getAddrs _ = error "Internal error: unexpected storage shape"

idOfAddr :: EVM.Expr EVM.EAddr -> T.Text
idOfAddr (EVM.SymAddr addr) = addr
idOfAddr _ = error "Internal error: upecting symbolic address"

-- | Checks that a contract map is a tree.
-- This ensures that each address is reachable by at most one store slot.
-- It assumes that each symbolic address is distinct (this is already checked
-- when creating the initial storage for the constructors).
checkTree :: ContractMap -> Error String ()
checkTree cmap = do
    traverseTree initAddr S.empty
    pure ()
  where
    traverseTree :: EVM.Expr EVM.EAddr -> S.Set (EVM.Expr EVM.EAddr) -> Error String (S.Set (EVM.Expr EVM.EAddr))
    traverseTree root seen | S.member root seen = throw (nowhere, "Detected aliasing in resulting store")
    traverseTree root seen =
        case M.lookup root cmap of
        Just (EVM.C _ storage _ _ _, _) ->
            foldValidation (\seen' (_, addr) -> traverseTree addr seen') (S.insert root seen) (getAddrs storage)
        _ -> error "Internal error: contract not found in map"


-- | Find the input space of an expr list
inputSpace :: [EVM.Expr EVM.End] -> [EVM.Prop]
inputSpace exprs = map aux exprs
  where
    aux :: EVM.Expr EVM.End -> EVM.Prop
    aux (EVM.Success c _ _ _) = EVM.pand c
    aux _ = error "List should only contain success behaviours"

-- | Check whether two lists of behaviours cover exactly the same input space
checkInputSpaces :: App m => SolverGroup -> [EVM.Expr EVM.End] -> [EVM.Expr EVM.End] -> m [EquivResult]
checkInputSpaces solvers l1 l2 = do
  let p1 = inputSpace l1
  let p2 = inputSpace l2

  conf <- readConfig

  let queries = fmap (assertProps conf) [ [ EVM.PNeg (EVM.por p1), EVM.por p2 ]
                                        , [ EVM.por p1, EVM.PNeg (EVM.por p2) ] ]

  results <- liftIO $ mapConcurrently (checkSat solvers Nothing) queries
  let results' = case results of
                   [r1, r2] -> [ toVRes "\x1b[1mThe following inputs are accepted by Act but not EVM\x1b[m" r1
                               , toVRes "\x1b[1mThe following inputs are accepted by EVM but not Act\x1b[m" r2 ]
                   _ -> error "Internal error: impossible"

  case all EVM.isQed results' of
    True -> pure [EVM.Qed]
    False -> pure $ filter (/= EVM.Qed) results'



-- | Checks whether all successful EVM behaviors are within the
--   interfaces specified by Act
checkAbi :: App m => SolverGroup -> Contract -> ContractMap -> m (Error String ())
checkAbi solver contract cmap = do
  showMsg "\x1b[1mChecking if the ABI of the contract matches the specification\x1b[m"
  let hevmstorage = translateCmap cmap
  let txdata = EVM.AbstractBuf "txdata"
  let selectorProps = assertSelector txdata <$> nubOrd (actSigs contract)
  evmBehvs <- getRuntimeBranches solver hevmstorage (txdata, []) [] 0 -- TODO what freshAddr goes here?
  conf <- readConfig
  let queries =  fmap (assertProps conf) $ filter (/= []) $ fmap (checkBehv selectorProps) evmBehvs
  res <- liftIO $ mapConcurrently (checkSat solver Nothing) queries
  checkResult (txdata, []) Nothing (fmap (toVRes msg) res)

  where
    actSig (Behaviour bname _ iface _ _ _ _) = T.pack $ makeIface bname iface
    actSigs (Contract _ behvs) = actSig <$> behvs

    checkBehv :: [EVM.Prop] -> EVM.Expr EVM.End -> [EVM.Prop]
    checkBehv assertions (EVM.Success cnstr _ _ _) = assertions <> cnstr
    checkBehv _ (EVM.Failure _ _ _) = []
    checkBehv _ (EVM.Partial _ _ _) = []
    checkBehv _ (EVM.ITE _ _ _) = error "Internal error: HEVM behaviours must be flattened"
    checkBehv _ (EVM.GVar _) = error "Internal error: unepected GVar"

    msg = "\x1b[1mThe following function selector results in behaviors not covered by the Act spec:\x1b[m"

checkContracts :: forall m. App m => SolverGroup -> StorageTyping -> M.Map Id (Contract, BS.ByteString, BS.ByteString, LayoutMode) -> m (Error String ())
checkContracts solvers store codeLayoutMap =
  let codemap = M.map (\(c,b1,b2,_) -> (c,b1,b2)) codeLayoutMap
      layoutmap = M.map (\(_,_,_,l) -> l) codeLayoutMap
      actenv = ActEnv codemap 0 (slotMap store layoutmap) initAddr Nothing in
  fmap (concatError def) $ forM (M.toList codemap) (\(_, (contract, initcode, bytecode)) -> do
    showMsg $ "\x1b[1mChecking contract \x1b[4m" <> nameOfContract contract <> "\x1b[m"
    (res, actenv') <- flip runStateT actenv $ checkConstructors solvers initcode bytecode contract
    case res of
      Success cmap -> do
        (behvs, _) <- flip runStateT actenv' $ checkBehaviours solvers contract cmap
        abi <- checkAbi solvers contract cmap
        pure $ behvs *> abi
      Failure e -> do
        showMsg $ "\x1b[1mFailure: Constructors of \x1b[4m" <> nameOfContract contract <> "\x1b[m are not equivalent"
        pure $ Failure e)
  where
    def = Success ()


readSelector :: EVM.Expr EVM.Buf -> EVM.Expr EVM.EWord
readSelector txdata =
    EVM.JoinBytes (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0)
                  (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0)
                  (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0)
                  (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0)
                  (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0)
                  (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0)
                  (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0) (EVM.LitByte 0)
                  (EVM.ReadByte (EVM.Lit 0x0) txdata)
                  (EVM.ReadByte (EVM.Lit 0x1) txdata)
                  (EVM.ReadByte (EVM.Lit 0x2) txdata)
                  (EVM.ReadByte (EVM.Lit 0x3) txdata)


assertSelector ::  EVM.Expr EVM.Buf -> T.Text -> EVM.Prop
assertSelector txdata sig =
  EVM.PNeg (EVM.PEq sel (readSelector txdata))
  where
    sel = EVM.Lit $ fromIntegral (EVM.abiKeccak (encodeUtf8 sig)).unFunctionSelector


-- * Utils

toVRes :: String -> EVM.SMTResult -> EquivResult
toVRes msg res = case res of
  EVM.Cex cex -> EVM.Cex (msg, cex)
  EVM.Unknown e -> EVM.Unknown e
  EVM.Qed -> EVM.Qed
  EVM.Error e -> EVM.Error e


checkResult :: App m => Calldata -> Maybe Sig -> [EquivResult] -> m (Error String ())
checkResult calldata sig res =
  case any EVM.isCex res of
    False ->
      case any EVM.isUnknown res || any EVM.isError res of
        True -> do
          showMsg "\x1b[41mNo discrepancies found but timeouts or solver errors were encountered. \x1b[m"
          pure $ Failure $ NE.singleton (nowhere, "Failure: Cannot prove equivalence.")
        False -> do
          showMsg "\x1b[42mNo discrepancies found.\x1b[m "
          pure $ Success ()
    True -> do
      let cexs = mapMaybe getCex res
      showMsg $ T.unpack . T.unlines $ [ "\x1b[41mNot equivalent.\x1b[m", "" , "-----", ""] <> (intersperse (T.unlines [ "", "-----" ]) $ fmap (\(msg, cex) -> T.pack msg <> "\n" <> formatCex (fst calldata) sig cex) cexs)
      pure $ Failure $ NE.singleton (nowhere, "Failure: Cannot prove equivalence.")

-- | Pretty prints a list of hevm behaviours for debugging purposes
showBehvs :: [EVM.Expr a] -> String
showBehvs behvs = T.unpack $ T.unlines $ fmap Format.formatExpr behvs

showProps :: [EVM.Prop] -> String
showProps props = T.unpack $ T.unlines $ fmap Format.formatProp props
