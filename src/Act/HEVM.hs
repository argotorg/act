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
{-# LANGUAGE ViewPatterns #-}

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
import qualified Control.Monad.Logic as Logic
import Control.Monad.Writer

import Act.HEVM_utils
import Act.Syntax.TypedExplicit as Act
import Act.Syntax
import Act.Error
import qualified Act.Syntax.Typed as TA
import Act.Syntax.Timing
import Act.Bounds
import Act.Type (hasSign)

import EVM.ABI (Sig(..))
import qualified EVM hiding (bytecode)
import qualified EVM.Types as EVM hiding (FrameState(..))
import EVM.Expr hiding (op2, inRange, div, xor, not, readStorage, Array)
import EVM.SymExec hiding (isPartial, reachable, formatCex)
import EVM.SMT (assertProps)
import EVM.Solvers
import EVM.Effects
import EVM.Format as Format
import EVM.Traversals
import qualified Data.Bifunctor as Bifunctor


type family ExprType a where
  ExprType 'AInteger  = EVM.EWord
  ExprType 'ABoolean  = EVM.EWord
  ExprType 'AContract = EVM.EWord
  ExprType 'AByteStr  = EVM.Buf

-- | The storage layout. Maps each contract type to a map that maps storage
-- variables to their slot, offset, and size in bytes in memory, as well as their signedness
-- For mappings and arrays, the size refers the type after full index saturation
type Layout = M.Map Id (LayoutMode, M.Map Id (Int,Int,Int,Bool))

data LayoutMode = SolidityLayout | VyperLayout
  deriving (Show)

-- | Maps each a sybmolic contract address to its Expr representation and contract id
type ContractMap = M.Map (EVM.Expr EVM.EAddr) (EVM.Expr EVM.EContract, Id)

-- | For each contract in the Act spec, put in a codemap its Act
-- specification, init code, and runtimecode. This is being looked up
-- when we encounter a constructor call.
type CodeMap = M.Map Id (Contract, BS.ByteString, BS.ByteString)

type EquivResult = EVM.ProofResult (String, EVM.SMTCex) String

-- | Initial symbolic address for contract deployment
initAddr :: EVM.Expr EVM.EAddr
initAddr = EVM.SymAddr "entrypoint"

-- | Generate storage layout from storage typing and layout mode map
slotMap :: StorageTyping -> M.Map Id LayoutMode -> Layout
slotMap store lmap =
  M.mapWithKey (\cid cstore ->
      let vars = sortOn (snd . snd) $ M.toList cstore
          layoutMode = fromJust $ M.lookup cid lmap
      in
        case vars of
          ("BALANCE", (_, -1)):vars' -> -- remove BALANCE from layout
            (layoutMode, M.fromList $ makeLayout layoutMode vars' 0 0)
          _ -> (layoutMode, M.fromList $ makeLayout layoutMode vars 0 0) -- shouldn't not be reachable
  ) store

makeLayout :: LayoutMode -> [(String, (ValueType, Integer))] -> Int -> Int -> [(Id, (Int,Int,Int,Bool))]
makeLayout _ [] _ _ = []
makeLayout SolidityLayout ((name,(typ,_)):vars) offset slot =
  if itFits then
    (name, (slot, offset, size, signExtendType typ)):makeLayout SolidityLayout vars (offset+size) slot
  else
    (name, (slot+1, 0, size, signExtendType typ)):makeLayout SolidityLayout vars size (slot+1)
  where
    size = sizeOfValue typ
    itFits = size <= 32 - offset
makeLayout VyperLayout ((name,(typ,_)):vars) _ slot =
  (name, (slot, 0, 32, signExtendType typ)):makeLayout VyperLayout vars 0 (slot+1)

-- Returns True if the values of a given type need to be sign extended
signExtendType :: ValueType -> Bool
signExtendType (ValueType (TInteger n Signed)) | n < 256 = True
signExtendType _ = False

signExtendArgType :: ArgType -> Bool
signExtendArgType (AbiArg (AbiIntType n)) | n < 256 = True
signExtendArgType _ = False

-- size of a storage item in bytes
sizeOfValue :: ValueType -> Int
sizeOfValue (ValueType t) = sizeOfTValue t

sizeOfTValue :: TValueType a -> Int
sizeOfTValue (TMapping _ _) = 32
sizeOfTValue t = sizeOfAbiType $ toAbiType t

sizeOfArgType :: ArgType -> Int
sizeOfArgType (AbiArg t) = sizeOfAbiType t
sizeOfArgType (ContractArg _ _) = sizeOfAbiType AbiAddressType

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

-- TODO: put callenv in here, not now though so as not to diff every single line
data ActEnv = ActEnv
  { codemap :: CodeMap                      -- ^ Map from contract Ids to their Act spec and bytecode
  , fresh   :: Int                          -- ^ Fresh variable counter
  , layout  :: Layout                       -- ^ Storage layout
  , caddr   :: EVM.Expr EVM.EAddr           -- ^ Current contract address
  , cid     :: Id                           -- ^ Current contract id
  , caller  :: Maybe (EVM.Expr EVM.EAddr)   -- ^ Caller address, empty if at top-level
  , layoutModeMap  :: M.Map Id LayoutMode   -- ^ Layout Mode used by contract, helpful for optimization
  }
  deriving (Show)

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

localCaddr :: Monad m => EVM.Expr EVM.EAddr -> Id -> ActT m a -> ActT m a
localCaddr caddr cid m = do
  env <- get
  let caddr' = env.caddr
  let cid' = env.cid
  let caller' = env.caller
  put (env { caddr = caddr, cid = cid, caller = Just caddr' })
  res <- m
  env' <- get
  put (env' { caddr = caddr', cid = cid', caller =  caller' })
  pure res

getCaller :: Monad m => ActT m (EVM.Expr EVM.EAddr)
getCaller = do
  env <- get
  case env.caller of
    Just c -> pure c
    Nothing -> pure $ EVM.SymAddr "caller" -- Zoe: not sure what to put here

getLayoutMode :: Monad m => ActT m LayoutMode
getLayoutMode = do
  env <- get
  pure $ fromJust $ flip M.lookup (env.layoutModeMap) (env.cid)

-- | Backtracking Act monad transformer for symbolic interpretation of different case paths
type ActBTT m a = ActT (WriterT [EVM.Prop] (Logic.LogicT m)) a

-- | Designate a path for each element of a foldable structure
fromFoldable :: (Monad m, Foldable f) => f a -> Logic.LogicT m a
fromFoldable f = Logic.LogicT $ \cons nil -> foldr cons nil f

-- | Collapse the backtracking Act monad transformer into a single Act monad transformer
-- by collecting results across all possible paths, along with their path conditions
collectAllPaths :: Monad m => ActBTT m a -> ActT m [(a, [EVM.Prop])]
collectAllPaths ndComp = do
  detState <- get
  innerM <- lift $ Logic.observeAllT $ runWriterT $ runStateT ndComp detState
  let ((res, ndStates), pathconds) = first unzip $ unzip innerM
  put $ determineActEnvs ndStates
  pure $ zip res pathconds
    where
      determineActEnvs envs = foldr1 appendEnvs envs
      -- Set the largest fresh value across all paths as the final one, so that no subsequent
      -- uses of the resulting contract map will clash with later generated symbolic addresses
      appendEnvs env1@ActEnv{fresh = f1} ActEnv{fresh = f2} | f1 < f2 = env1{fresh = f2}
      appendEnvs env1 _ = env1

-- * Act translation

-- | Enforce that all storage variables are within their type's range in the prestate.
-- This is necessary for Vyper, since a variable's value corresponds to the slot's whole 256 bits,
-- so we need to enforce that no garbage is present in the extra bits.
-- Since act preserves the invariant of respecting types' ranges, successful equivalence checking
-- also guarantees said property for the bytecode.
-- NOTE: Make sure to write to the whole slot as well in Vyper mode!
prestateStorageBounds :: forall m . Monad m => ContractMap -> [TypedRef] -> ActT m [EVM.Prop]
prestateStorageBounds contractMap locs = do
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

-- | Extend an EVM.End expression with additional path conditions
addPathCondition :: [EVM.Prop] -> EVM.Expr EVM.End -> EVM.Expr EVM.End
addPathCondition pcs' (EVM.Success pcs tc b m) = EVM.Success (pcs' ++ pcs) tc b m
addPathCondition _ end = end

-- | The ABI requires that values of types with size less than 256 bits are padded, using sign extension where necessary
-- This function generates checks that the padding is valid, i.e. no garbage exists in the extra bits
signExtendArgConstraints :: Interface -> [EVM.Prop]
signExtendArgConstraints (Interface _ args) = mapMaybe signExtendArgConstraint args
  where
  signExtendArgConstraint :: Arg -> Maybe EVM.Prop
  signExtendArgConstraint (Arg atyp x) =
    let (sgnExt, size) = (signExtendArgType atyp, sizeOfArgType atyp) in
    if sgnExt then
      pure $ EVM.PEq (EVM.Var $ T.pack x) (EVM.SEx (EVM.Lit (fromIntegral size - 1)) (EVM.Var $ T.pack x))
    else Nothing

translateConstructor :: Monad m => BS.ByteString -> Constructor -> ContractMap -> ActT m ([(EVM.Expr EVM.End, ContractMap)], Calldata, Sig, [EVM.Prop])
translateConstructor bytecode (Constructor cid iface _ preconds cases _ _) cmap = do
  let initmap = M.insert initAddr (initcontract, cid) cmap
  -- After `addBounds`, `preconds` contains all integer locations that have been constrained in the Act spec.
  -- All must be enforced again to avoid discrepancies. Necessary for Vyper.
  -- Note that since all locations are already in `preconds`,
  -- there is no need to look at other fields.
  bounds <- prestateStorageBounds initmap $ nub $ concatMap locsFromConstrCase cases <> concatMap locsFromExp preconds
  ends <- collectAllPaths $ do
    -- Branch into a path for each constructor case
    ccase <- lift . lift $ fromFoldable cases
    translateConstructorCase bytecode initmap (snd calldata) bounds preconds ccase
  pure (integratePathConds <$> ends, calldata, ifaceToSig cid iface, bounds)
  where
    calldata = makeCtrCalldata iface
    initcontract = EVM.C { EVM.code    = EVM.RuntimeCode (EVM.ConcreteRuntimeCode bytecode)
                         , EVM.storage = EVM.ConcreteStore mempty
                         , EVM.tStorage = EVM.ConcreteStore mempty
                         , EVM.balance = EVM.Lit 0
                         , EVM.nonce   = Just 1
                         }
    integratePathConds ((end, cm), pcs) = (addPathCondition pcs end, cm)

translateConstructorCase :: Monad m => BS.ByteString -> ContractMap -> [EVM.Prop] -> [EVM.Prop] -> [Exp ABoolean] -> Ccase -> ActBTT m (EVM.Expr EVM.End, ContractMap)
translateConstructorCase bytecode initmap cdataprops bounds preconds (Case _ casecond upds) = do
  preconds' <- mapM (toProp initmap emptyEnv) preconds
  casecond' <- toProp initmap emptyEnv casecond
  cmap' <- applyUpdates initmap initmap emptyEnv upds
  let acmap = abstractCmap initAddr cmap'
  pure (simplify $ EVM.Success (cdataprops <> preconds' <> bounds <> [casecond'] <> symAddrCnstr cmap') mempty (EVM.ConcreteBuf bytecode) (M.map fst cmap'), acmap)
  -- TODO: check: why was it symAddrCnstr acmap before?

symAddrCnstr :: ContractMap -> [EVM.Prop]
symAddrCnstr cmap =
    (\(a1, a2) -> EVM.PNeg (EVM.PEq (EVM.WAddr a1) (EVM.WAddr a2))) <$> comb (M.keys cmap)

ifaceToSig :: Id -> Interface -> Sig
ifaceToSig name (Interface _ args) = Sig (T.pack name) (fmap fromdecl args)
  where
    fromdecl (Arg argtype _) = argToAbiType argtype

translateBehv :: App m => ContractMap -> Behaviour -> ActT m ([(EVM.Expr EVM.End, ContractMap)], [EVM.Prop])
translateBehv cmap (Behaviour behvName _ iface _ preconds cases _)  = do
  let argConstraints = signExtendArgConstraints iface
  -- We collect all integer bounds from all cases of a given behaviour.
  -- These bounds are set as preconditions for all cases of a behaviour,
  -- even if some are not necessary for all cases, because the input space
  -- must be compared against that of the symbolic execution. On that side,
  -- it is not possible to distinguish between cases, so we make no distinction
  -- here either.
  bounds <- prestateStorageBounds cmap $ nub $ concatMap locsFromCase cases <> concatMap locsFromExp preconds
  ends <- collectAllPaths $ do
    -- Branch into a path for each transition case
    bcase <- lift . lift $ fromFoldable cases
    (translateBehvCase cmap (snd behvCalldata) bounds preconds) bcase
  pure (first (addPathCondition argConstraints) <$> (integratePathConds <$> ends), bounds)
  where
    behvCalldata = makeCalldata behvName iface
    integratePathConds ((end, cm), pcs) = (addPathCondition pcs end, cm)

translateBehvCase :: Monad m => ContractMap -> [EVM.Prop] -> [EVM.Prop] -> [Exp ABoolean] -> Bcase -> ActBTT m (EVM.Expr EVM.End, ContractMap)
translateBehvCase cmap cdataprops bounds preconds (Case _ casecond (upds, ret)) = do
  preconds' <- mapM (toProp cmap emptyEnv) preconds
  casecond' <- toProp cmap emptyEnv casecond
  ret' <- returnsToExpr cmap emptyEnv ret
  cmap' <- applyUpdates cmap cmap emptyEnv upds
  let acmap = abstractCmap initAddr (M.map (first simplify) cmap')
  pure (simplify $ EVM.Success (preconds' <> bounds <> [casecond'] <> cdataprops <> symAddrCnstr cmap') mempty ret' (M.map fst cmap'), acmap)

-- | Show a contract map for debugging purposes
showCmap :: ContractMap -> String
showCmap cmap = intercalate "\n\n" $ map (\(addr, (c, cid)) -> showContract addr cid c) (M.toList cmap)
  where
    showContract :: EVM.Expr EVM.EAddr -> Id -> EVM.Expr EVM.EContract -> String
    showContract addr cid (EVM.C _ storage _ bal _) =
       "Contract: " ++ cid ++ " at address " ++ show addr ++ ":\n" ++
       "{ storage = " ++ show storage ++ "\n. balance = " ++ show bal ++ "}" ++ show cid
    showContract _ _ (EVM.GVar _) = "GVar"


applyUpdates :: Monad m => ContractMap -> ContractMap -> CallEnv -> [StorageUpdate] -> ActBTT m ContractMap
applyUpdates readMap writeMap callenv upds = foldM (\wm upd -> applyUpdate readMap wm callenv upd) writeMap upds

applyUpdate :: Monad m => ContractMap -> ContractMap -> CallEnv -> StorageUpdate -> ActBTT m ContractMap
applyUpdate readMap writeMap callenv (Update typ@VType ref e) = writeToRef readMap writeMap callenv (TRef typ SLHS ref) (TExp typ e)

writeToRef :: Monad m => ContractMap -> ContractMap -> CallEnv -> TypedRef -> TypedExp -> ActBTT m ContractMap
writeToRef readMap writeMap callenv (TRef _ _ ref) (TExp typ e) | isBalanceRef ref = do
    case typ of
        TInteger _ _ -> do
          caddr' <- baseAddr writeMap callenv ref
          e' <- toExpr readMap callenv e
          let (contract, cid) = fromMaybe (error $ "Internal error: contract not found\n" <> show e) $ M.lookup caddr' writeMap
          pure $ M.insert caddr' (updateBalance e' contract, cid) writeMap
        _ -> error $ "Internal error: BALANCE can only be assigned an integer value, found " ++ show typ
  where
    updateBalance :: EVM.Expr EVM.EWord -> EVM.Expr EVM.EContract -> EVM.Expr EVM.EContract
    updateBalance bal (EVM.C code storage tstorage _ nonce) = EVM.C code storage tstorage bal nonce
    updateBalance _ (EVM.GVar _) = error "Internal error: contract cannot be a global variable"

writeToRef readMap writeMap callenv tref@(TRef _ _ ref) (TExp typ e) = do
  caddr' <- baseAddr writeMap callenv ref
  (addr, offset, size, signextend, _) <- refOffset writeMap callenv ref
  let (contract, cid) = fromMaybe (error $ "Internal error: contract not found\n" <> show e) $ M.lookup caddr' writeMap
  case typ of
    TAddress ->
        case isCreate e of
          Just newCid -> do
            fresh <- getFreshIncr
            let freshAddr = EVM.SymAddr $ "freshSymAddr" <> (T.pack $ show fresh)
            writeMap' <- localCaddr freshAddr newCid $ createCastedContract readMap writeMap callenv freshAddr e
            let prevValue = readStorage addr contract
            let e' = storedValue (EVM.WAddr freshAddr) prevValue offset size signextend
            pure $ (M.insert caddr' (updateNonce (updateStorage (EVM.SStore addr e') contract), cid)) writeMap'
          Nothing -> do
            e' <- toExpr readMap callenv e
            let prevValue = readStorage addr contract
            let e'' = storedValue e' prevValue offset size signextend
            pure $ M.insert caddr' (updateStorage (EVM.SStore addr e'') contract, cid) writeMap
    TContract _ -> do
        case isCreate e of
          Just newCid -> do
            fresh <- getFreshIncr
            let freshAddr = EVM.SymAddr $ "freshSymAddr" <> (T.pack $ show fresh)
            writeMap' <- localCaddr freshAddr newCid $ createContract readMap writeMap callenv freshAddr e
            let prevValue = readStorage addr contract
            let e' = storedValue (EVM.WAddr freshAddr) prevValue offset size signextend
            pure $ (M.insert caddr' (updateNonce (updateStorage (EVM.SStore addr e') contract), cid)) writeMap'
          Nothing -> do
            e' <- toExpr readMap callenv e
            let prevValue = readStorage addr contract
            let e'' = storedValue e' prevValue offset size signextend
            pure $ M.insert caddr' (updateStorage (EVM.SStore addr e'') contract, cid) writeMap
    TByteStr -> error "Bytestrings not supported"
    TInteger _ _ -> do
        e' <- toExpr readMap callenv e
        let prevValue = readStorage addr contract
        let e'' = storedValue e' prevValue offset size signextend
        pure $ M.insert caddr' (updateStorage (EVM.SStore addr e'') contract, cid) writeMap
    TBoolean -> do
        e' <- toExpr readMap callenv e
        let prevValue = readStorage addr contract
        let e'' = storedValue e' prevValue offset size signextend
        pure $ M.insert caddr' (updateStorage (EVM.SStore addr e'') contract, cid) writeMap
    TMapping _ _ -> do
        let expansion = expandMappingUpdate tref e
        foldM (\wm (tr,te) -> writeToRef readMap wm callenv tr te) writeMap expansion
    TArray _ _ -> error "arrays TODO"
    TStruct _ -> error "structs TODO"
    TUnboundedInt -> error "Internal error: Unbounded Integer after typechecking" -- Zoe: the typechecker will introduce unbounded integers, let's handle them the same way as integers
-- TODO test with out of bounds assignments
  where
    storedValue :: EVM.Expr EVM.EWord -> EVM.Expr EVM.EWord -> EVM.Expr EVM.EWord -> Int -> Bool -> EVM.Expr EVM.EWord
    storedValue new prev offset size signextend =
        let offsetBits = EVM.Mul (EVM.Lit 8) offset in
        let maxVal = EVM.Lit $ (2 ^ (8 * size)) - 1 in
        let mask = EVM.Xor (EVM.SHL offsetBits maxVal) (EVM.Lit MAX_UINT) in
        let newmask = if signextend then EVM.And (EVM.Not mask) else id in
        let newShifted = EVM.SHL offsetBits new in
        EVM.Or (newmask newShifted) (EVM.And prev mask)

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

    isCreate :: Exp a -> Maybe Id
    isCreate (Create _ cid _ _) = Just cid
    isCreate (Address _ cid (Create _ _ _ _)) = Just cid
    isCreate _ = Nothing

    expandMappingUpdate :: TypedRef -> Exp AMapping -> [(TypedRef, TypedExp)]
    expandMappingUpdate r (Mapping _ keyType@VType valType@VType es) =
      let refPairs = (\(k,v) -> (TRef valType SRHS (RMapIdx nowhere r (TExp keyType k)), v)) <$> es in
      case toSType valType of
        SMapping -> concatMap (uncurry expandMappingUpdate) refPairs
        _ -> map (Bifunctor.second (TExp valType)) refPairs
    expandMappingUpdate (TRef _ _ r) (MappingUpd _ r' _ _ _) | refToRHS r /= refToRHS r' =
      error "Mapping update reference inconsistency, past typing"
    expandMappingUpdate r (MappingUpd _ _ keyType@VType valType@VType es) =
      let refPairs = (\(k,v) -> (TRef valType SRHS (RMapIdx nowhere r (TExp keyType k)), v)) <$> es in
      case toSType valType of
        SMapping -> concatMap (uncurry expandMappingUpdate) refPairs
        _ -> map (Bifunctor.second (TExp valType)) refPairs
    expandMappingUpdate _ e'@(ITE _ _ _ _) = error $ "Internal error: expecting flat expression. got: " <> show e'
    expandMappingUpdate _ (VarRef _ _ _) = error "Internal error: variable assignment of mappings not expected"

isBalanceRef :: Ref k -> Bool
isBalanceRef (SVar _ _ _ name) = name == "BALANCE"
isBalanceRef CVar{} = False
isBalanceRef RArrIdx{} = False
isBalanceRef RMapIdx{} = False
isBalanceRef (RField _ _ _ x) = x == "BALANCE"

createCastedContract :: Monad m => ContractMap -> ContractMap -> CallEnv -> EVM.Expr EVM.EAddr -> Exp AInteger -> ActBTT m ContractMap
createCastedContract readMap writeMap callenv freshAddr (Address _ _ (Create pn cid args b)) =
 createContract readMap writeMap callenv freshAddr (Create pn cid args b)
createCastedContract _ _ _ _ _ = error "Internal error: constructor call expected"

createContract :: Monad m => ContractMap -> ContractMap -> CallEnv -> EVM.Expr EVM.EAddr -> Exp AContract -> ActBTT m ContractMap
createContract readMap writeMap callenv freshAddr (Create _ cid args cv) = do
  codemap <- getCodemap
  case M.lookup cid codemap of
    Just (Contract (Constructor _ _ _ _ [] _ _) _, _, _) ->
      error $ "Internal error: Contract " <> cid <> " has no cases from which to form map\n" <> show codemap
    Just (Contract (Constructor _ iface _ _ cases _ _) _, _, bytecode) -> do
      -- Create a path for each case
      ccase <- lift . lift $ fromFoldable cases
      applyCase ccase
      where
        applyCase :: Monad m => Ccase -> ActBTT m ContractMap
        applyCase (Case _ caseCond upds) = do
          callenv' <- makeCallEnv readMap callenv iface args cv
          caseCond' <- toProp readMap callenv' caseCond
          tell [caseCond']
          applyUpdates readMap (M.insert freshAddr (contract, cid) writeMap) callenv' upds

        contract = EVM.C { EVM.code  = EVM.RuntimeCode (EVM.ConcreteRuntimeCode bytecode)
                           , EVM.storage = EVM.ConcreteStore mempty
                           , EVM.tStorage = EVM.ConcreteStore mempty
                           , EVM.balance = EVM.Lit 0
                           , EVM.nonce = Just 1
                           }
    Nothing -> error "Internal error: constructor not found"
createContract _ _ _ _ _ = error "Internal error: constructor call expected"

type CallEnv = (M.Map Id (EVM.Expr EVM.EWord))

emptyEnv :: CallEnv
emptyEnv = M.empty

-- | Create constructor call environment
makeCallEnv :: Monad m => ContractMap -> CallEnv -> Interface -> [TypedExp] -> Maybe (Exp AInteger) -> ActBTT m CallEnv
makeCallEnv cmap callenv (Interface _ decls) args cv = do
  lst <- zipWithM (\(Arg _ x) texp -> do
    wexpr <- typedExpToWord cmap callenv texp
    pure (x, wexpr)) decls args
  lst' <- case cv of
    Just e -> do
      wexpr <- toExpr cmap callenv e
      pure $ lst ++ [("CALLVALUE", wexpr)]
    Nothing -> pure lst
  pure $ M.fromList lst'

-- | Expand n LSBs to full 256 word
lsbsToWord :: Int -> Bool -> LayoutMode -> EVM.Expr EVM.EWord -> EVM.Expr EVM.EWord
lsbsToWord 32 _ _ = id
lsbsToWord _ _ VyperLayout = id
lsbsToWord n signext SolidityLayout = case signext of
  True -> EVM.SEx (EVM.Lit (fromIntegral n `div` 8 - 1))
  False -> EVM.And (EVM.Lit $ 2^n - 1)

returnsToExpr :: Monad m => ContractMap -> CallEnv -> Maybe TypedExp -> ActBTT m (EVM.Expr EVM.Buf)
returnsToExpr _ _ Nothing = pure $ EVM.ConcreteBuf ""
returnsToExpr cmap callenv (Just r) = typedExpToBuf cmap callenv r

wordToBuf :: EVM.Expr EVM.EWord -> EVM.Expr EVM.Buf
wordToBuf w = EVM.WriteWord (EVM.Lit 0) w (EVM.ConcreteBuf "")

wordToProp :: EVM.Expr EVM.EWord -> EVM.Prop
wordToProp w = EVM.PNeg (EVM.PEq w (EVM.Lit 0))

typedExpToBuf :: Monad m => ContractMap -> CallEnv -> TypedExp -> ActBTT m (EVM.Expr EVM.Buf)
typedExpToBuf cmap callenv expr =
  case expr of
    TExp styp e -> expToBuf cmap callenv styp e

typedExpToWord :: Monad m => ContractMap -> CallEnv -> TypedExp -> ActBTT m (EVM.Expr EVM.EWord)
typedExpToWord cmap callenv te = do
    case te of
        TExp vtyp e -> case vtyp of
            TInteger n sgn -> do
              lm <- getLayoutMode
              let sgnext = sgn == Signed
              lsbsToWord n sgnext lm <$> toExpr cmap callenv e

            TUnboundedInt -> toExpr cmap callenv e
            TContract _ -> toExpr cmap callenv e -- TODO: is this correct?
            TAddress -> toExpr cmap callenv e
            TBoolean -> toExpr cmap callenv e
            TByteStr -> error "Bytestring in unexpected position"
            TArray _ _ -> error "TODO arrays"
            TStruct _ -> error "TODO structs"
            TMapping _ _ -> error "TODO Mappings" -- TODO

expToBuf :: Monad m => forall a. ContractMap -> CallEnv -> TValueType a -> Exp a  -> ActBTT m (EVM.Expr EVM.Buf)
expToBuf cmap callenv vtyp e = do
  case vtyp of
    (TInteger n sgn) -> do
      e' <- toExpr cmap callenv e
      lm <- getLayoutMode
      let sgnext = sgn == Signed
      pure $ EVM.WriteWord (EVM.Lit 0) (lsbsToWord n sgnext lm e') (EVM.ConcreteBuf "")
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
getPosition :: Layout -> Id -> Id -> (Int, Int, Int, Bool, LayoutMode)
getPosition layout cid name =
  case M.lookup cid layout of
    Just (lm, m) -> case M.lookup name m of
      Just (p1,p2,p3,p4) -> (p1,p2,p3,p4,lm)
      Nothing -> error $ "Internal error: invalid variable name: " <> show name
    Nothing -> error "Internal error: invalid contract name"

-- | For the given storage reference, it returs the memory slot, the offset
-- of the value within the slot, and the size of the value.
refOffset :: Monad m => ContractMap -> CallEnv -> Ref k -> ActBTT m (EVM.Expr EVM.EWord, EVM.Expr EVM.EWord, Int, Bool, LayoutMode)
refOffset _ _ (CVar _ _ _) = error "Internal error: ill-typed entry"
refOffset _ _ (SVar _ _ cid name) = do
  layout <- getLayout
  let (slot, off, size, signextend, layoutMode) = getPosition layout cid name
  pure (EVM.Lit (fromIntegral slot), EVM.Lit $ fromIntegral off, size, signextend, layoutMode)
refOffset cmap callenv (RMapIdx _ (TRef (TMapping _ t) _ ref) ix) = do
  (slot, _, _, _, layoutMode) <- refOffset cmap callenv ref
  buf <- typedExpToBuf cmap callenv ix
  let concatenation = case layoutMode of
        SolidityLayout -> buf <> (wordToBuf slot)
        VyperLayout -> (wordToBuf slot) <> buf
  let addr = (EVM.keccak concatenation)
  let size =  case layoutMode of
        SolidityLayout -> sizeOfValue t
        VyperLayout -> 32
  pure (addr, EVM.Lit 0, size, signExtendType t, layoutMode)
refOffset _ _ (RField _ _ cid name) = do
  layout <- getLayout
  let (slot, off, size, signextend, layoutMode) = getPosition layout cid name
  pure (EVM.Lit (fromIntegral slot), EVM.Lit $ fromIntegral off, size, signextend, layoutMode)
refOffset _ _ (RArrIdx _ _ _ _) = error "TODO"
refOffset _ _ (RMapIdx _ (TRef _ _ _) _) = error "Internal error: Map Index into non-map reference"


-- | Get the address of the contract whoose storage contrains the given
-- reference
baseAddr :: Monad m => ContractMap -> CallEnv -> Ref k -> ActBTT m (EVM.Expr EVM.EAddr)
baseAddr _ _ (SVar _ _ _ _) = getCaddr
baseAddr _ _ (CVar _ _ _) = error "Internal error: ill-typed entry"
baseAddr cmap callenv (RField _ ref _ _) = do
  expr <- refToExp (cmap) callenv ref
  case simplify expr of
    EVM.WAddr symaddr -> pure symaddr
    e -> error $ "Internal error: did not find a symbolic address: " <> show e <> " " <> show ref
baseAddr cmap callenv (RMapIdx _ (TRef _ _ ref) _) = baseAddr cmap callenv ref
baseAddr cmap callenv (RArrIdx _ ref _ _) = baseAddr cmap callenv ref


ethEnvToWord :: Monad m => CallEnv -> EthEnv -> ActT m (EVM.Expr EVM.EWord)
ethEnvToWord callenv Callvalue =
    case M.lookup "CALLVALUE" callenv of
        Just e -> pure e
        Nothing -> pure EVM.TxValue
ethEnvToWord _ Caller = do
  c <- getCaller
  pure $ EVM.WAddr c
ethEnvToWord _ Origin = pure $ EVM.WAddr (EVM.SymAddr "origin") -- Why not: pure $ EVM.Origin
ethEnvToWord _ This = do
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
  (Eq _ TUnboundedInt e1 e2) -> op2 EVM.PEq e1 e2
  (Eq _ (TContract _) e1 e2) -> op2 EVM.PEq e1 e2
  (Eq _ TAddress e1 e2) -> op2 EVM.PEq e1 e2
  (Eq _ TBoolean e1 e2) -> op2 EVM.PEq e1 e2
  (Eq _ _ _ _) -> error "unsupported"
  (NEq _ (TInteger _ _) e1 e2) -> do
    e <- op2 EVM.PEq e1 e2
    pure $ EVM.PNeg e
  (NEq _ TUnboundedInt e1 e2) -> do
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
  (ITE _ b e1 e2) -> do
    b' <- toProp cmap callenv b
    e1' <- toProp cmap callenv e1
    e2' <- toProp cmap callenv e2
    pure $ EVM.PAnd (EVM.PImpl b' e1') (EVM.PImpl (EVM.PNeg b') e2')
  (VarRef _ _ ref) -> do
    refPaths <- collectAllPaths $ refToExp cmap callenv ref
    pure $ pathsToProp refPaths (EVM.PEq (EVM.Lit 0) . EVM.IsZero)
  (InRange _ t e) -> do
    paths <- collectAllPaths $ inRange cmap callenv t e
    pure $ pathsToProp paths (EVM.PEq (EVM.Lit 0) . EVM.IsZero)
  where
    op2 :: Monad m => forall b. (EVM.Expr (ExprType b) -> EVM.Expr (ExprType b) -> EVM.Prop) -> Exp b -> Exp b -> ActT m EVM.Prop
    op2 op e1 e2 = do
      paths <- collectAllPaths $ do
        e1' <- toExpr cmap callenv e1
        e2' <- toExpr cmap callenv e2
        pure $ op e1' e2'
      pure $ pathsToProp paths id

    pop2 :: Monad m => forall a. (EVM.Prop -> EVM.Prop -> a) -> Exp ABoolean -> Exp ABoolean -> ActT m a
    pop2 op e1 e2 = do
      e1' <- toProp cmap callenv e1
      e2' <- toProp cmap callenv e2
      pure $ op e1' e2'

    pathsToProp :: [(a, [EVM.Prop])] -> (a -> EVM.Prop) -> EVM.Prop
    pathsToProp paths propper = case NE.nonEmpty paths of
      Just nePaths -> foldr1 (EVM.PAnd) $ (condProp propper) <$> nePaths
      Nothing -> error "Internal error: no paths found!"
      where
        condProp :: (a -> EVM.Prop) -> (a,[EVM.Prop]) -> EVM.Prop
        condProp f (p,cs) = EVM.PImpl (EVM.pand cs) $ f p


pattern MAX_UINT :: EVM.W256
pattern MAX_UINT = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

-- TODO: this belongs to HEVM
stripMods :: EVM.Expr a -> EVM.Expr a
stripMods = mapExpr go
  where
    go :: EVM.Expr a -> EVM.Expr a
    go (EVM.Mod a (EVM.Lit MAX_UINT)) = a
    go a = a

toExpr :: forall a m. Monad m => ContractMap -> CallEnv -> TA.Exp a Timed -> ActBTT m (EVM.Expr (ExprType a))
toExpr cmap callenv =  fmap stripMods . go
  where
    go :: Monad m => Exp a -> ActBTT m (EVM.Expr (ExprType a))
    go = \case
      -- booleans
      (And _ e1 e2) -> op2 EVM.And e1 e2
      (Or _ e1 e2) -> op2 EVM.Or e1 e2
      (Impl _ e1 e2) -> op2 (EVM.Or . EVM.Not) e1 e2
      (Neg _ e1) -> do
        e1' <- toExpr cmap callenv e1
        pure $ EVM.IsZero e1' -- XXX why EVM.Not fails here?
      (Act.LT _ e1 e2) -> signedop2 EVM.LT EVM.SLT e1 e2
      (LEQ _ e1 e2) -> signedop2 EVM.LEq (EVM.IsZero `comp2` (flip EVM.SLT)) e1 e2
      (GEQ _ e1 e2) -> signedop2 EVM.GEq (EVM.IsZero `comp2` EVM.SLT) e1 e2
      (Act.GT _ e1 e2) -> signedop2 EVM.GT (flip EVM.SLT) e1 e2
      (LitBool _ b) -> pure $ EVM.Lit (fromIntegral $ fromEnum b)
      -- integers
      (Add _ e1 e2) -> op2 EVM.Add e1 e2
      (Sub _ e1 e2) -> op2 EVM.Sub e1 e2
      (Mul _ e1 e2) -> op2 EVM.Mul e1 e2
      (Div _ e1 e2) -> signedop2 EVM.Div EVM.SDiv e1 e2
      (Mod _ e1 e2) -> signedop2 EVM.Mod EVM.SMod e1 e2
      (Exp _ e1 e2) -> op2 EVM.Exp e1 e2
      (LitInt _ n) -> pure $ EVM.Lit (fromIntegral n)
      (IntEnv _ env) -> ethEnvToWord callenv env
      -- bounds
      (IntMin _ n) -> pure $ EVM.Lit (fromIntegral $ intmin n)
      (IntMax _ n) -> pure $ EVM.Lit (fromIntegral $ intmax n)
      (UIntMin _ n) -> pure $ EVM.Lit (fromIntegral $ uintmin n)
      (UIntMax _ n) -> pure $ EVM.Lit (fromIntegral $ uintmax n)
      (InRange _ t e) -> inRange cmap callenv t e
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
      (Eq _ TUnboundedInt e1 e2) -> op2 EVM.Eq e1 e2
      (Eq _ (TContract _) e1 e2) -> op2 EVM.Eq e1 e2
      (Eq _ TBoolean e1 e2) -> op2 EVM.Eq e1 e2
      (Eq _ TAddress e1 e2) -> op2 EVM.Eq e1 e2
      (Eq _ _ _ _) -> error "unsupported"

      (NEq _ (TInteger _ _) e1 e2) -> do
        e <- op2 EVM.Eq e1 e2
        pure $ EVM.Not e
      (NEq _ TUnboundedInt e1 e2) -> do
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
      (VarRef _ TUnboundedInt ref) -> refToExp cmap callenv ref
      (VarRef _ TBoolean ref) -> refToExp cmap callenv ref
      (VarRef _ TAddress ref) -> refToExp cmap callenv ref
      (VarRef _ (TContract _) ref) -> refToExp cmap callenv ref

      (ITE _ bc e1 e2) -> do
        bc' <- toProp cmap callenv bc
        -- Create 2 paths
        (caseCond, caseExpr) <- lift . lift $ fromFoldable [(bc',e1),(EVM.PNeg bc',e2)]
        tell [caseCond]
        toExpr cmap callenv caseExpr

      (Address _ _ e') -> toExpr cmap callenv e'
      e ->  error $ "TODO: " <> show e

    op2 :: Monad m => forall b c. (EVM.Expr (ExprType c) -> EVM.Expr (ExprType c) -> b) -> Exp c -> Exp c -> ActBTT m b
    op2 op e1 e2 = do
      e1' <- toExpr cmap callenv e1
      e2' <- toExpr cmap callenv e2
      pure $ op e1' e2'

    signedop2 :: Monad m => forall b. (EVM.Expr EVM.EWord -> EVM.Expr EVM.EWord -> b)
                                   -> (EVM.Expr EVM.EWord -> EVM.Expr EVM.EWord -> b) -> Exp AInteger -> Exp AInteger -> ActBTT m b
    signedop2 uop sop e1 e2 = do
      e1' <- toExpr cmap callenv e1
      e2' <- toExpr cmap callenv e2
      if hasSign Unsigned e1 && hasSign Unsigned e2 then pure $ uop e1' e2'
      else if hasSign Signed e1 && hasSign Signed e2 then pure $ sop e1' e2'
      else error "toExpr: Cannot compare expressions of different sign" -- TODO: implement smarter sign detection using entailments

    comp2 :: (b -> c) -> (a1 -> a2 -> b) -> a1 -> a2 -> c
    comp2 = (.) . (.)



-- | Extract a value from a slot using its offset and size
extractValue ::  EVM.Expr EVM.EWord -> EVM.Expr EVM.EWord -> Int -> Bool -> LayoutMode -> EVM.Expr EVM.EWord
extractValue slot offset size signext lm =
    let bits = EVM.Mul offset (EVM.Lit 8) in
    lsbsToWord (size*8) signext lm (EVM.SHR bits slot)

refToExp :: forall m k. Monad m => ContractMap -> CallEnv -> Ref k -> ActBTT m (EVM.Expr EVM.EWord)
--  reference to balance
refToExp cmap callenv ref | isBalanceRef ref = do
    caddr <- baseAddr cmap callenv ref
    case M.lookup caddr cmap of
      Just (EVM.C _ _ _ bal _, _) -> pure bal
      Just (EVM.GVar _, _) -> error "Internal error: contract cannot be a global variable"
      Nothing -> error $ "Internal error: contract not found " <> show caddr <> "\nmap:" <> show cmap
-- calldata variable
refToExp _ callenv (CVar _ typ x) = do
    lm <- getLayoutMode
    case M.lookup x callenv of
      Just e -> pure $ mask lm e
      Nothing -> pure $ mask lm $ fromCalldataFramgment $ symAbiArg (T.pack x) (argToAbiType typ)

  where
    fromCalldataFramgment :: CalldataFragment -> EVM.Expr EVM.EWord
    fromCalldataFramgment (St _ word) = word
    fromCalldataFramgment _ = error "Internal error: only static types are supported"

    mask lm = case (signExtendArgType typ, sizeOfArgType typ) of
        (signext, size) -> lsbsToWord (size*8) signext lm

refToExp cmap callenv r = do
  caddr <- baseAddr cmap callenv r
  (slot, offset, size, signext, lm) <- refOffset cmap callenv r
  let word = accessStorage cmap slot caddr
  pure $ extractValue word offset size signext lm

accessStorage :: ContractMap -> EVM.Expr EVM.EWord -> EVM.Expr EVM.EAddr -> EVM.Expr EVM.EWord
accessStorage cmap slot addr = case M.lookup addr cmap of
  Just (EVM.C _ storage _ _ _, _) ->
    EVM.SLoad slot storage
  Just (EVM.GVar _, _) -> error "Internal error: contract cannot be a global variable"
  Nothing -> error $ "Internal error: contract not found " <> show addr <> "\nmap:" <> show cmap

evmMinSigned :: EVM.W256
evmMinSigned = ((^) :: EVM.W256 -> EVM.W256 -> EVM.W256) 2 255

evmMaxAddr :: EVM.W256
evmMaxAddr = ((^) :: EVM.W256 -> EVM.W256 -> EVM.W256) 2 160 - 1

inRange :: Monad m => ContractMap -> CallEnv -> TValueType AInteger -> Exp AInteger -> ActBTT m (EVM.Expr EVM.EWord)
-- if the type has the type of machine word then check per operation
inRange cmap callenv (TInteger 256 s) e = checkOp cmap callenv 256 s e
inRange cmap callenv (TInteger n s) e@(Mul {}) | n > 128 = checkOp cmap callenv n s e
inRange cmap callenv (TInteger n s) e@(Mod {}) = checkOp cmap callenv n s e
inRange cmap callenv (TInteger n s) e@(Div {}) = checkOp cmap callenv n s e
inRange cmap callenv (TInteger n Unsigned) e = do
  e' <- toExpr cmap callenv e
  pure $ EVM.LEq e' (EVM.Lit $ 2^n - 1)
inRange cmap callenv (TInteger n Signed) e = do
  e' <- toExpr cmap callenv e
  pure $ EVM.Eq e' (EVM.SEx (EVM.Lit $ fromIntegral n `div` 8 - 1) e')
inRange cmap callenv TAddress e = do
  e' <- toExpr cmap callenv e
  pure $ EVM.LEq e' (EVM.Lit evmMaxAddr)
inRange _ _ TUnboundedInt _ = error "Internal error: inRange: cannot receive unbounded integer type"


checkOp :: Monad m => ContractMap -> CallEnv -> Int -> IntSign -> Exp AInteger -> ActBTT m (EVM.Expr EVM.EWord)
checkOp _ _ _ _ (LitInt _ i) = pure $ EVM.Lit $ fromIntegral $ fromEnum $ i <= (fromIntegral (maxBound :: Word256))
checkOp _ _ _ _ (VarRef _ _ _)  = pure $ EVM.Lit 1
checkOp cmap callenv _ Unsigned e@(Add _ e1 _) = do
  e' <- toExpr cmap callenv e
  e1' <- toExpr cmap callenv e1
  pure $ EVM.LEq e1' e'
checkOp cmap callenv _ Signed e@(Add _ e1 e2) = do
  e' <- toExpr cmap callenv e
  e1' <- toExpr cmap callenv e1
  e2' <- toExpr cmap callenv e2
  pure $ foldr1 EVM.And [ EVM.IsZero (EVM.And (EVM.SLT e' e2') (EVM.IsZero (EVM.SLT e1' (EVM.Lit 0))))
                        , EVM.IsZero (EVM.And (EVM.IsZero (EVM.SLT e' e2')) ((EVM.SLT e1' (EVM.Lit 0)))) ]
checkOp cmap callenv _ Unsigned e@(Sub _ e1 _) = do
  e' <- toExpr cmap callenv e
  e1' <- toExpr cmap callenv e1
  pure $ EVM.LEq e' e1'
checkOp cmap callenv _ Signed e@(Sub _ e1 e2) = do
  e' <- toExpr cmap callenv e
  e1' <- toExpr cmap callenv e1
  e2' <- toExpr cmap callenv e2
  pure $ foldr1 EVM.And [ EVM.IsZero (EVM.And (EVM.SLT e' e1') (EVM.SLT e2' (EVM.Lit 0)))
                        , EVM.IsZero (EVM.And (EVM.SLT e1' e') (EVM.IsZero (EVM.SLT e2' (EVM.Lit 0)))) ]
checkOp cmap callenv 256 Signed (Mul _ e1 e2) = do
  e1' <- toExpr cmap callenv e1
  e2' <- toExpr cmap callenv e2
  pure $ foldr1 EVM.And [ EVM.Or (EVM.Eq (EVM.SDiv (EVM.Mul e1' e2') e1') e2') (EVM.LEq e1' (EVM.Lit 0))
                        , EVM.IsZero (EVM.And (EVM.SLT e1' (EVM.Lit 0)) (EVM.Eq e2' (EVM.Lit evmMinSigned))) ]
checkOp cmap callenv n sign (Mul _ e1 e2) = do
  e1' <- toExpr cmap callenv e1
  e2' <- toExpr cmap callenv e2
  let (evmDiv, mask) = case sign of
        Signed -> (EVM.SDiv, EVM.SEx (EVM.Lit $ fromIntegral n `div` 8 - 1))
        Unsigned -> (EVM.Div, EVM.And (EVM.Lit $ 2^n-1))
  pure (EVM.Or (EVM.IsZero e1') (EVM.Eq (evmDiv (mask (EVM.Mul e1' e2')) (e1')) e2'))
checkOp cmap callenv n Signed (Div _ e1 e2) = do
  e1' <- toExpr cmap callenv e1
  e2' <- toExpr cmap callenv e2
  pure $ foldr1 EVM.And [ EVM.Or (EVM.IsZero $ EVM.Eq e2' (EVM.Lit $ -1)) (EVM.IsZero $ EVM.Eq e1' (EVM.Lit $ -2^(n-1)))
                        , EVM.IsZero (EVM.Eq e2' (EVM.Lit 0)) ]
checkOp cmap callenv _ Unsigned (Div _ _ e2) = do
  e2' <- toExpr cmap callenv e2
  pure (EVM.IsZero (EVM.Eq (EVM.Lit 0) e2'))
checkOp cmap callenv _ _ (Mod _ _ e2) = do
  e2' <- toExpr cmap callenv e2
  pure (EVM.IsZero (EVM.Eq (EVM.Lit 0) e2'))
checkOp _ _ _ _ (Address _ _ _) = pure $ EVM.Lit 1
checkOp _ _ _ _ (Exp _ _ _) = error "Internal error: checkOp: TODO: EXP"
checkOp _ _ _ _ e@(IntMin _ _)  =  error $ "Internal error: checkOp:invalid in range expression" ++ show e
checkOp _ _ _ _ e@(IntMax _ _)  =  error $ "Internal error: checkOp:invalid in range expression" ++ show e
checkOp _ _ _ _ e@(UIntMin _ _) =  error $ "Internal error: checkOp:invalid in range expression" ++ show e
checkOp _ _ _ _ e@(UIntMax _ _) =  error $ "Internal error: checkOp:invalid in range expression" ++ show e
checkOp _ _ _ _ (ITE _ _ _ _) =  error "TODO ITE in checkOp"
checkOp _ _ _ _ (IntEnv _ _) = pure $ EVM.Lit 1


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
  let contracts = contractsFromIFace iface
  (cmaps, checks) <- mapAndUnzipM getContractState contracts

  let finalmap = M.unions (cmap:cmaps)

  check <- checkAliasing finalmap cmaps
  pure (finalmap, check <* sequenceA_ checks <* checkUniqueAddr (cmap:cmaps))

  where
    -- extract contracts present in the interface
    contractsFromIFace :: Interface -> [(Id, Id)]
    contractsFromIFace (Interface _ decls) = mapMaybe castingDecl decls
      where
      castingDecl (Arg (ContractArg _ cid) name) = Just (name, cid)
      castingDecl _ = Nothing

    getContractState :: App m => (Id, Id) -> ActT m (ContractMap, Error String ())
    getContractState (x, cid) = do
      let addr = EVM.SymAddr $ T.pack x -- TODO freshen symbolic addresses to ensure global uniqueness
      codemap <- getCodemap
      case M.lookup cid codemap of
        Just (Contract (Constructor cname' iface' _ preconds' ((Case _ _ upds):_) _ _) _, _, bytecode) -> do
          (icmap, check) <- getInitContractState solvers cname' iface' preconds' M.empty
          let contract = EVM.C { EVM.code  = EVM.RuntimeCode (EVM.ConcreteRuntimeCode bytecode)
                               , EVM.storage = EVM.ConcreteStore mempty
                               , EVM.tStorage = EVM.ConcreteStore mempty
                               , EVM.balance = EVM.Lit 0
                               , EVM.nonce = Just 1
                               }
          let icmap' = M.insert addr (contract, cid) icmap
          cmap' <- localCaddr addr cname' $ collectAllPaths $ applyUpdates icmap' icmap' emptyEnv upds
          pure (abstractCmap addr (fst $ head cmap'), check)
        Just (Contract (Constructor _ _ _ _ [] _ _) _, _, _) ->
          error $ "Internal error: Contract " <> cid <> " has no cases\n"
        Nothing -> error $ "Internal error: Contract " <> cid <> " not found\n" <> show codemap

    checkAliasing :: App m => ContractMap -> [ContractMap] -> ActT m (Error String ())
    checkAliasing cmap' cmaps = do
      let allkeys = M.foldrWithKey (\k (_, cid) l -> (k, cid):l) [] <$> cmaps
      -- gather all tuples that must be distinct
      let allpairs = concatMap (\(l1, l2) -> (,) <$> l1 <*> l2) $ comb allkeys
      -- Require them to be distinct, if they have the same contract type. We assume that addresses assumed to be of different types
      -- are distinct
      let dquery = EVM.por $ (\((a1, c1),(a2, c2)) ->
                                if c1 == c2 then EVM.PEq (EVM.WAddr a1) (EVM.WAddr a2) else EVM.PBool False) <$> allpairs
      preconds' <- mapM (toProp cmap' emptyEnv) preconds
      lift $ checkQueries (dquery:preconds')

    checkQueries :: App m => [EVM.Prop] -> m (Error String ())
    checkQueries queries = do
      conf <- readConfig
      res <- liftIO $ checkSat solvers Nothing (assertProps conf queries)
      checkResult (makeCalldata cname iface) Nothing [toVRes msg res]

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
checkConstructors solvers initcode runtimecode (Contract ctor@(Constructor cname iface payable preconds _ _ _)  _) = do
  -- Construct the initial contract state
  (actinitmap, errors) <- getInitContractState solvers cname iface preconds M.empty
  let (hevminitmap, checks') = translateCmap actinitmap payable
  -- Translate Act constructor to Expr
  fresh <- getFresh
  (actbehvs, calldata, sig, bounds) <- translateConstructor runtimecode ctor actinitmap
  let (behvs', fcmaps) = unzip actbehvs
    -- Symbolically execute bytecode
    -- TODO check if contrainsts about preexistsing fresh symbolic addresses are necessary
  solbehvs <- lift $ removeFails <$> getInitcodeBranches solvers initcode payable hevminitmap calldata (checks' ++ bounds) fresh

  -- Check equivalence
  lift $ showMsg "\x1b[1mChecking if constructor results are equivalent.\x1b[m"
  res1 <- lift $ checkResult calldata (Just sig) =<< checkEquiv solvers solbehvs behvs'
  lift $ showMsg "\x1b[1mChecking if constructor input spaces are the same.\x1b[m"
  res2 <- lift $ checkResult calldata (Just sig) =<< checkInputSpaces solvers solbehvs behvs'
  pure $ traverse_ (checkStoreIsomorphism (head fcmaps)) (tail fcmaps) *> errors *> res1 *> res2 *> checkTree (head fcmaps) *> Success (head fcmaps)
  where
    removeFails branches = filter isSuccess branches


checkBehaviours :: forall m. App m => SolverGroup -> Contract -> ContractMap -> ActT m (Error String ())
checkBehaviours solvers (Contract _ behvs) actstorage = do
  fresh <- getFresh
  (fmap $ concatError def) $ forM behvs $ \behv@(Behaviour name _ iface payable preconds _ _) -> do
    let calldata = makeCalldata name iface
    let sig = ifaceToSig name iface
    -- construct initial contract state for the transition by adding the contracts passed as arguments
    (initstore, errors) <- getInitContractState solvers name iface preconds actstorage
    -- translate Act behaviour to Expr
    (actbehv,bounds) <- translateBehv initstore behv
    let (behvs', fcmaps) = unzip actbehv
    -- translate Act contract map to hevm contract map
    let (hevmstorage, checks) = translateCmap initstore payable
    -- symbolically execute bytecode
    solbehvs <- lift $ removeFails <$> getRuntimeBranches solvers hevmstorage calldata (checks ++ bounds) fresh

    lift $ showMsg $ "\x1b[1mChecking behavior \x1b[4m" <> name <> "\x1b[m of Act\x1b[m"
    -- equivalence check
    lift $ showMsg "\x1b[1mChecking if behaviour is matched by EVM\x1b[m"
    res1 <- lift $ checkResult calldata (Just sig) =<< checkEquiv solvers solbehvs behvs'
    -- input space exhaustiveness check
    lift $ showMsg "\x1b[1mChecking if the input spaces are the same\x1b[m"
    res2 <- lift $ checkResult calldata (Just sig) =<< checkInputSpaces solvers solbehvs behvs'
    pure $ traverse_ (checkStoreIsomorphism actstorage) (fcmaps) *> res1 *> res2 *> errors

  where
    removeFails branches = filter isSuccess branches
    def = Success ()


translateCmap :: ContractMap -> IsPayable -> ([(EVM.Expr EVM.EAddr, EVM.Contract)], [EVM.Prop])
translateCmap cmap payable = foldl go ([], []) (M.toList cmap)
  where
    go (storage, props) (addr, (c, _)) =
        let (contract, newprops) = toContract addr c in
        ((addr, contract):storage, newprops ++ props)

    toContract :: EVM.Expr EVM.EAddr -> EVM.Expr EVM.EContract -> (EVM.Contract, [EVM.Prop])
    toContract addr (EVM.C code storage tstorage balance nonce) =
      (EVM.Contract
        { EVM.code        = code
        , EVM.storage     = storage
        , EVM.tStorage    = tstorage
        , EVM.origStorage = storage
        , EVM.balance     = if payable == Payable && addr == initAddr then EVM.Add EVM.TxValue balance else balance
        , EVM.nonce       = nonce
        , EVM.codehash    = EVM.hashcode code
        , EVM.opIxMap     = EVM.mkOpIxMap code
        , EVM.codeOps     = EVM.mkCodeOps code
        , EVM.external    = False
        }
      , [EVM.PLEq balance (EVM.Add EVM.TxValue balance) | payable == Payable && addr == initAddr])
    toContract _ (EVM.GVar _) = error "Internal error: contract cannot be gvar"


-- TODO: Lefteris: Shouldn't this only check for typed addresses?
-- If so, this means that detecting addresses should rely on StorageTyping,
-- not just on tracking hevm's symbolic addresses
abstractCmap :: EVM.Expr EVM.EAddr -> ContractMap -> ContractMap
abstractCmap this cmap =
  pruneContractState this $ M.mapWithKey makeContract cmap
  where
    traverseStorage ::  EVM.Expr EVM.EAddr -> EVM.Expr EVM.Storage -> EVM.Expr EVM.Storage
    traverseStorage addr (EVM.SStore offset (simplify . (EVM.And $ EVM.Lit evmMaxAddr) -> EVM.WAddr symaddr) storage) =
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

-- Since only one address fits in each slot, we weed to find the topmost one stored in each slot
slotAddress :: EVM.Expr EVM.EWord -> Maybe (EVM.Expr EVM.EWord)
slotAddress = fmap fst . go
  where
  -- TODO: think about how necessary this is
    go :: EVM.Expr EVM.EWord -> Maybe (EVM.Expr EVM.EWord, Int)
    go e@(EVM.WAddr _) = pure (e, 0)
    go (EVM.And e1 e2) = case (go e1, go e2) of
      (Just _, Just _) -> error "Internal error: overlapping addresses in slot"
      (Nothing, Nothing) -> error "Internal error: no address assigned in slot"
      (Just (_), Nothing) -> undefined
      (Nothing, Just (_)) -> undefined
    go _ = Nothing

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
          else throw (nowhere, "1: The shape of the resulting map is not preserved.")
        (Nothing, Nothing) -> visit addrs1 addrs2 (M.insert a1 a2 map1) (M.insert a2 a1 map2) ((a1, a2): discovered)
        (_, _) -> throw (nowhere, "2: The shape of the resulting map is not preserved.")
    visit _ _ _ _  _ = throw (nowhere, "3: The shape of the resulting map is not preserved.")

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
  let (hevmstorage, _) = translateCmap cmap NonPayable
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
      layoutmap = M.map (\(_,_,_,l) -> l) codeLayoutMap in
  fmap (concatError def) $ forM (M.toList codemap) (\(_, (contract, initcode, bytecode)) -> do
    let cid = nameOfContract contract
        actenv = ActEnv codemap 0 (slotMap store layoutmap) initAddr cid Nothing layoutmap
    showMsg $ "\x1b[1mChecking contract \x1b[4m" <> cid <> "\x1b[m"
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
