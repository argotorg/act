{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# Language TypeApplications #-}
{-# Language ScopedTypeVariables #-}
{-# Language NamedFieldPuns #-}
{-# Language DataKinds #-}
{-# Language KindSignatures #-}
{-# LANGUAGE ApplicativeDo #-}
{-# Language TupleSections #-}

module Act.Type (typecheck, lookupVars, globalEnv, Err) where

import Prelude hiding (GT, LT)

import EVM.ABI
import Data.Map.Strict    (Map)
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..), (<|))
import qualified Data.List.NonEmpty as NonEmpty (toList, singleton)
import qualified Data.Map.Strict    as Map
import Data.Typeable ( Typeable, (:~:)(Refl), eqT )
import Type.Reflection (typeRep)

import Control.Monad (when)
import Data.Functor
import Data.List.Extra (unsnoc)
import Data.Function (on)
import Data.Foldable
import Data.Traversable
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Ordered (OMap)
import qualified Data.Map.Ordered as OM

import Act.Syntax
import Act.Syntax.Timing
import Act.Syntax.Untyped qualified as U
import Act.Syntax.TypedImplicit
import Act.Error

import Data.Type.Equality (TestEquality(..))
import Data.Singletons


type Err = Error String

-- | Typecheck and then detect possible circularities in constructor call graph
typecheck :: U.Act -> Err Act
typecheck act = typecheck' act `bindValidation` topologicalSort

-- | Main typechecking function.
typecheck' :: U.Act -> Err Act
typecheck' (U.Main contracts) = Act store <$> traverse (checkContract store constructors) contracts
                             <* noDuplicateContracts
                             <* noDuplicateBehaviourNames
                             <* noDuplicateInterfaces
                             <* traverse noDuplicateVars [creates | U.Contract (U.Constructor _ _ _ _ creates _ _) _ <- contracts]
  where
    store = lookupVars contracts
    constructors = lookupConstructors contracts

    transitions = concatMap (\(U.Contract _ ts) -> ts) contracts

    noDuplicateContracts :: Err ()
    noDuplicateContracts = noDuplicates [(pn,contract) | U.Contract (U.Constructor pn contract _ _ _ _ _) _ <- contracts]
                           $ \c -> "Multiple definitions of Contract " <> c

    noDuplicateVars :: U.Creates -> Err ()
    noDuplicateVars (U.Creates assigns) = noDuplicates (fmap fst . fromAssign <$> assigns)
                                          $ \x -> "Multiple definitions of Variable " <> x

    noDuplicateInterfaces :: Err ()
    noDuplicateInterfaces =
      noDuplicates
        [(pn, contract ++ "." ++ (makeIface iface)) | U.Transition pn _ contract iface _ _ _ <- transitions]
        $ \c -> "Multiple definitions of Interface " <> c

    noDuplicateBehaviourNames :: Err ()
    noDuplicateBehaviourNames =
      noDuplicates
        [(pn, contract ++ "." ++ behav) | U.Transition pn behav contract _ _ _ _ <- transitions]
        $ \c -> "Multiple definitions of Behaviour " <> c

    -- Generic helper
    noDuplicates :: [(Pn,Id)] -> (Id -> String) -> Err ()
    noDuplicates xs errmsg = traverse_ (throw . fmap errmsg) . nub . duplicatesBy ((==) `on` snd) $ xs
      where
        -- gathers duplicate entries in list based on a custom equality predicate.
        duplicatesBy :: Eq a => (a -> a -> Bool) -> [a] -> [a]
        duplicatesBy _ [] = []
        duplicatesBy f (y:ys) =
          let e = [x | x <- ys , f y x]
              prependIfNotEmpty :: [a] -> a -> [a]
              prependIfNotEmpty [] _ = []
              prependIfNotEmpty a b = b : a
          in (prependIfNotEmpty e y) <> duplicatesBy f ys


-- | Sort contracts topologically so there are no backward edges in
-- the constructor call graph. Throw an error if a cycle is detected.
topologicalSort :: Act -> Err Act
topologicalSort (Act store contracts) =
  -- OM.assoc will return the nodes in the reverse order they were
  -- visited (post-order). Reversing this gives us a topological
  -- ordering of the nodes.
  Act store . reverse . map snd . OM.assocs <$> foldValidation doDFS OM.empty (map fst calls)
  where
    doDFS :: OMap Id Contract -> Id -> Err (OMap Id Contract)
    doDFS visited v = if OM.member v visited then pure visited
      else dfs Set.empty visited v

    dfs :: Set Id -> OMap Id Contract -> Id -> Err (OMap Id Contract)
    dfs stack visited v
      | Set.member v stack = throw (nowhere, "Detected cycle in constructor calls")
      | OM.member v visited = pure visited
      | otherwise = let (ws, code) = adjacent v in
                    let stack' = Set.insert v stack in
                    (OM.|<) (v, code) <$> foldValidation (dfs stack') visited ws

    adjacent :: Id -> ([Id], Contract)
    adjacent v = case Map.lookup v g of
        Just ws -> ws
        Nothing -> error "Internal error: node must be in the graph"

    calls = fmap findCreates contracts
    g = Map.fromList calls

    -- map a contract name to the list of contracts that it calls and its code
    findCreates :: Contract -> (Id, ([Id], Contract))
    findCreates c@(Contract (Constructor cname _ _ _ _ _) _) = (cname, (createsFromContract c <> pointersFromContract c, c))

--- Finds storage declarations from constructors
lookupVars :: [U.Contract] -> Store
lookupVars = foldMap $ \case
  U.Contract (U.Constructor _ contract _ _ (U.Creates assigns) _ _) _ ->
    Map.singleton contract . Map.fromList $ addSlot $ snd . fromAssign <$> assigns
  where
    addSlot :: [(Id, SlotType)] -> [(Id, (SlotType, Integer))]
    addSlot l = zipWith (\(name, typ) slot -> (name, (typ, slot))) l [0..]

-- | A map containing the interfaces of all available constructors together with pointer constraints
type Constructors = Map Id [ArgType]

-- | Construct the constructor map for the given spec
lookupConstructors :: [U.Contract] -> Constructors
lookupConstructors = foldMap $ \case
  U.Contract (U.Constructor _ contract (Interface _ decls) _ _ _ _) _ ->
    Map.singleton contract (map (\(Decl t _) -> t) decls)

-- | Extracts what we need to build a 'Store' and to verify that its names are
-- unique.
fromAssign :: U.Assign -> (Pn, (Id, SlotType))
fromAssign (U.AssignVal (U.StorageVar pn typ var) _) = (pn, (var, typ))
fromAssign (U.AssignMapping (U.StorageVar pn typ var) _) = (pn, (var, typ))


-- | The type checking environment.
data Env = Env
  { contract     :: Id                           -- ^ The name of the current contract.
  , store        :: Map Id SlotType              -- ^ This contract's storage entry names and their types.
  , theirs       :: Store                        -- ^ Mapping from contract names to a map of their entry names and their types.
  , calldata     :: Map Id ArgType               -- ^ The calldata var names and their types.
  , constructors :: Constructors                 -- ^ Interfaces of constructors
  }
  deriving (Show)

-- | Environment with globally available variables.
globalEnv :: [(EthEnv, ActType)]
globalEnv =
  [(Callvalue, AInteger),
   (Caller, AInteger),
   (Blockhash, AInteger),
   (Blocknumber, AInteger),
   (Difficulty, AInteger),
   (Timestamp, AInteger),
   (Gaslimit, AInteger),
   (Coinbase, AInteger),
   (Chainid, AInteger),
   (This, AInteger),
   (Origin, AInteger),
   (Nonce, AInteger),
   (Calldepth, AInteger)
  ]


mkEnv :: Id -> Store -> Constructors -> Env
mkEnv contract store constructors = Env
  { contract = contract
  , store    = Map.map fst $ fromMaybe mempty (Map.lookup contract store)
  , theirs   = store
  , calldata = mempty
  , constructors = constructors
  }

-- Add calldata to environment
addCalldata :: [Decl] -> Env -> Env
addCalldata decls env = env{ calldata = abiVars }
  where
   abiVars = Map.fromList $ map (\(Decl typ var) -> (var, typ)) decls

-- Type check a contract
checkContract :: Store -> Constructors -> U.Contract -> Err Contract
checkContract store constructors (U.Contract constr@(U.Constructor _ cid _ _ _ _ _) trans) =
  Contract <$> checkConstructor env constr <*> (concat <$> traverse (checkBehavior env) trans) <* namesConsistent
  where
    env :: Env
    env = mkEnv cid store constructors

    namesConsistent :: Err ()
    namesConsistent =
      traverse_ (\(U.Transition pn _ cid' _ _ _ _) -> assert (errmsg pn cid') (cid == cid')) trans

    errmsg pn cid' = (pn, "Behavior must belong to contract " <> show cid <> " but belongs to contract " <> cid')


-- Type check a behavior
checkBehavior :: Env -> U.Transition -> Err [Behaviour]
checkBehavior env (U.Transition _ name contract iface@(Interface _ decls) iffs cases posts) =
  traverse_ (checkDecl env') decls *>
  noIllegalWilds *>
  -- constrain integer calldata variables (TODO: other types)
  fmap fmap (makeBehv <$> checkIffs env' iffs <*> traverse (checkExpr env' SBoolean Atomic) posts)
  <*> traverse (checkCase env') normalizedCases
  where
    -- Add calldata variables and pointers to the typing environment
    env' = addCalldata decls env

    noIllegalWilds :: Err ()
    noIllegalWilds = case cases of
      U.Branches bs -> for_ (init bs) $ \c@(U.Case p _ _) ->
                          ((when (isWild c) ((throw (p, "Wildcard pattern must be last case")):: Err ())) :: Err ())

    -- translate wildcards into negation of other branches and translate a single case to a wildcard
    normalizedCases :: [U.Case]
    normalizedCases = case cases of
     U.Branches bs ->
        let
          (rest, lastCase@(U.Case pn _ post)) = case unsnoc bs of
                                                  Just r -> r
                                                  Nothing -> error "Internal error: branches cannot be empty"
          negation = U.ENot nowhere $
                        foldl (\acc (U.Case _ e _) -> U.EOr nowhere e acc) (U.BoolLit nowhere False) rest
        in rest ++ [if isWild lastCase then U.Case pn negation post else lastCase]

    -- Construct a behavior node
    makeBehv :: [Exp ABoolean Untimed] -> [Exp ABoolean Timed] -> ([Exp ABoolean Untimed], [StorageUpdate], Maybe (TypedExp Timed)) -> Behaviour
    makeBehv pres posts' (casecond,storage,ret) = Behaviour name contract iface pres casecond posts' storage ret

checkConstructor :: Env -> U.Constructor -> Err Constructor
checkConstructor env (U.Constructor _ contract (Interface _ decls) iffs (U.Creates assigns) postcs invs) =
  do
    traverse_ (checkDecl env') decls
    stateUpdates <- concat <$> traverse (checkAssign env') assigns
    iffs' <- checkIffs envNoStorage iffs
    traverse_ (validStorage env') assigns
    ensures :: [Exp a Untimed] <- traverse (checkExpr env' SBoolean Atomic) postcs
    invs' <- fmap (Invariant contract [] [] . PredUntimed) <$> traverse (checkExpr env' SBoolean Atomic) invs
    pure $ Constructor contract (Interface contract decls) iffs' ensures invs' stateUpdates
  where
    env' = addCalldata decls env
    -- type checking environment prior to storage creation of this contract
    envNoStorage = env'{ store = mempty }

-- | Checks that an argument declaration is valid. This consists of
-- checking that for a calldata variable of contract type A,
-- A is a valid contract type.
checkDecl :: Env -> U.Decl -> Err ()
checkDecl Env{theirs} (Decl (ContractArg p c) _) =
  case Map.lookup c theirs of
    Nothing -> throw (p, "Contract " <> c <> " is not a valid contract type")
    Just _ -> pure ()
checkDecl _ _ = pure ()


-- | Check if the types of storage variables are valid
validStorage :: Env -> U.Assign -> Err ()
validStorage env (U.AssignVal (U.StorageVar p t _) _) = validSlotType env p t
validStorage env (U.AssignMapping (U.StorageVar p t _) _) = validSlotType env p t

-- | Check if the a contract type is valid in an environment
validType :: Env -> Pn -> ValueType -> Err ()
validType Env{theirs} p (ContractType c) =
  maybe (throw (p, "Contract " <> c <> " is not a valid contract type")) (\_ -> pure ()) $ Map.lookup c theirs
validType _ _ _ = pure ()

validKey :: Pn -> ValueType -> Err ()
validKey p (ContractType _) = throw (p, "Mappings cannot have contract indices")
validKey _ _ = pure ()

validSlotType :: Env -> Pn -> SlotType -> Err ()
validSlotType env p (StorageMapping ks res) = traverse_ (\k -> validType env p k <* validKey p k) ks <* validType env p res
validSlotType env p (StorageValue t) = validType env p t


-- | Type checks a case, returning typed versions of its preconditions, rewrites and return value.
checkCase :: Env -> U.Case -> Err ([Exp ABoolean Untimed], [StorageUpdate], Maybe (TypedExp Timed))
checkCase env c@(U.Case _ pre post) = do
  -- TODO isWild checks for WildExp, but WildExp is never generated
  if' <- traverse (checkExpr env SBoolean Atomic) $ if isWild c then [U.BoolLit nowhere True] else [pre]
  (storage,return') <- checkPost env post
  pure (if',storage,return')

flattenArrayAbiTypeErr :: Pn -> String -> AbiType -> Err (AbiType, NonEmpty Int)
flattenArrayAbiTypeErr p err t = maybe (throw (p,err)) Success $ flattenArrayAbiType t

-- Check the initial assignment of a storage variable
checkAssign :: Env -> U.Assign -> Err [StorageUpdate]
checkAssign env@Env{contract} (U.AssignVal (U.StorageVar pn (StorageValue vt@(FromVType typ)) name) expr)
  = sequenceA [checkExpr envNoStorage typ (shapeFromVT typ vt) expr `bindValidation` \te ->
               findContractType env te `bindValidation` \ctyp ->
               _Update (_Item vt (SVar pn contract name)) te <$ validContractType pn vt ctyp]
  where
    -- type checking environment prior to storage creation of this contract
    envNoStorage = env { store = mempty }

checkAssign env (U.AssignMapping (U.StorageVar pn (StorageMapping (keyType :| _) valType) name) defns)
  = for defns $ \def -> checkDefn pn envNoStorage keyType valType name def
  where
    -- type checking environment prior to storage creation of this contract
    envNoStorage = env { store = mempty }

checkAssign _ (U.AssignVal (U.StorageVar pn (StorageMapping _ _) _) _)
  = throw (pn, "Cannot assign a single expression to a composite type")

checkAssign _ (U.AssignMapping (U.StorageVar pn (StorageValue _) _) _)
  = throw (pn, "Cannot assign initializing mapping to a non-mapping slot")

-- ensures key and value types match when assigning a defn to a mapping
-- TODO: handle nested mappings
checkDefn :: Pn -> Env -> ValueType -> ValueType -> Id -> U.Mapping -> Err StorageUpdate
checkDefn pn env@Env{contract} keyType vt@(FromVType valType) name (U.Mapping k val) =
  _Update
  <$> (_Item vt . SMapping nowhere (SVar pn contract name) vt <$> checkIxs env (getPosn k) [k] [keyType])
  <*> checkExpr env valType (shapeFromVT valType vt) val

-- | Type checks a cases actions, returning typed versions of its storage updates and return expression.
checkPost :: Env -> U.Post -> Err ([StorageUpdate], Maybe (TypedExp Timed))
checkPost env (U.Post storage maybeReturn) = do
  returnexp <- traverse (inferExpr env) maybeReturn
  storage' <- checkEntries storage
  pure (storage', castRet <$> returnexp)
  where
    checkEntries :: [U.Storage] -> Err [StorageUpdate]
    checkEntries entries = for entries $ \case
      U.Update loc val -> checkStorageExpr env loc val

    castRet :: TypedExp t -> TypedExp t
    castRet (TExp SContract _ e) =
      TExp SInteger Atomic $ Address (fromJust $ orElse (findContractType env e) (error "Internal error: castRet")) e
    castRet t = t

checkEntry :: forall t k. Typeable t => Env -> SRefKind k -> U.Entry -> Err (SlotType, Maybe Id, Ref k t)
checkEntry Env{contract,store,calldata} kind (U.EVar p name) = case (kind, Map.lookup name store, Map.lookup name calldata) of
  (_, Just _, Just _) -> throw (p, "Ambiguous variable " <> name)
  (SStorage, Just typ@(StorageValue (ContractType c)), Nothing) -> pure (typ, Just c, SVar p contract name)
  (SStorage, Just typ, Nothing) -> pure (typ, Nothing, SVar p contract name)
  (SCalldata, Nothing, Just (AbiArg typ)) -> pure (StorageValue (PrimitiveType typ), Nothing, CVar p typ name)
  (SCalldata, Nothing, Just (ContractArg _ c)) -> pure (StorageValue (PrimitiveType AbiAddressType), Just c, CVar p AbiAddressType name)
  (SStorage, _, Just _) -> error "Internal error: Expected storage variable but found calldata variable"
  (SCalldata, Just _, _) -> error "Internal error: Expected calldata variable but found storage variable"
  (_, Nothing, Nothing) -> throw (p, "Unknown variable " <> show name)
checkEntry env kind (U.EIndexed p e args) =
  checkEntry env kind e `bindValidation` \(styp, _, ref) -> case styp of
    StorageValue (PrimitiveType typ) ->
        flattenArrayAbiTypeErr' typ `bindValidation` \(_,sizes) ->
        checkArrayIxs env p args (toList sizes) `bindValidation` \ixs ->
        pure (StorageValue (PrimitiveType (derefAbiType (length ixs) typ)), Nothing, SArray p ref (PrimitiveType (derefAbiType (length ixs) typ)) ixs)
        where
          flattenArrayAbiTypeErr' = flattenArrayAbiTypeErr p "Variable of value type cannot be indexed into"
          derefAbiType :: Int -> AbiType -> AbiType
          derefAbiType n (AbiArrayType _ a) | n > 0 = derefAbiType (n-1) a
          derefAbiType _ a = a
    StorageValue (ContractType _) -> throw (p, "Expression should have a mapping type" <> show e)
    StorageMapping argtyps restyp ->
        (StorageValue restyp, Nothing,) . SMapping p ref restyp <$> checkIxs env p args (NonEmpty.toList argtyps)
checkEntry env@Env{theirs} kind (U.EField p e x) =
  checkEntry env kind e `bindValidation` \(_, oc, ref) -> case oc of
    Just c -> case Map.lookup c theirs of
      Just cenv -> case Map.lookup x cenv of
        Just (st@(StorageValue (ContractType c')), _) -> pure (st, Just c', SField p ref c x)
        Just (st, _) -> pure (st, Nothing, SField p ref c x)
        Nothing -> throw (p, "Contract " <> c <> " does not have field " <> x)
      Nothing -> error $ "Internal error: Invalid contract type " <> show c
    _ -> throw (p, "Expression should have a contract type" <> show e)

validateEntry :: forall t k. Typeable t => Env -> SRefKind k -> U.Entry -> Err (ValueType, Ref k t)
validateEntry env kind entry =
  checkEntry env kind entry `bindValidation` \(typ, oc, ref) -> case typ of
    StorageValue t -> case oc of
                        Just cid -> pure (ContractType cid, ref)
                        _ -> pure (t, ref)
    StorageMapping _ _  -> throw (getPosEntry entry, "Top-level expressions cannot have mapping type")

-- | Typecheck a storage update
checkStorageExpr :: Env -> U.Entry -> U.Expr -> Err StorageUpdate
checkStorageExpr env entry expr =
  validateEntry env SStorage entry `bindValidation` \(vt@(FromVType typ), ref) ->
  checkExpr env typ (shapeFromVT typ vt) expr `bindValidation` \te ->
  findContractType env te `bindValidation` \ctyp ->
  _Update (_Item vt ref) te <$ validContractType (getPosn expr) vt ctyp


validContractType :: Pn -> ValueType -> Maybe Id -> Err ()
validContractType pn (ContractType c1) (Just c2) =
  assert (pn, "Assignment to storage variable was expected to have contract type " <> c1 <> " but has contract type " <> c2) (c1 == c2)
validContractType pn (ContractType c1) Nothing =
  throw (pn, "Assignment to storage variable was expected to have contract type " <> c1)
validContractType _ _ _ = pure ()

checkIffs :: Env -> U.Iff -> Err [Exp ABoolean Untimed]
checkIffs env exps = traverse (checkExpr env SBoolean Atomic) exps

-- | If an `inrange e` predicate appears in the source code, then the inrange
-- predicate is propagated to all subexpressions of `e`. This elaboration step
-- happens here.
genInRange :: AbiType -> Exp AInteger t -> [Exp ABoolean t]
genInRange t e@(LitInt _ _) = [InRange nowhere t e]
genInRange t e@(VarRef _ _ _ _)  = [InRange nowhere t e]
genInRange t e@(Add _ e1 e2) = [InRange nowhere t e] <> genInRange t e1 <> genInRange t e2
genInRange t e@(Sub _ e1 e2) = [InRange nowhere t e] <> genInRange t e1 <> genInRange t e2
genInRange t e@(Mul _ e1 e2) = [InRange nowhere t e] <> genInRange t e1 <> genInRange t e2
genInRange t e@(Div _ e1 e2) = [InRange nowhere t e] <> genInRange t e1 <> genInRange t e2
genInRange t e@(Mod _ e1 e2) = [InRange nowhere t e] <> genInRange t e1 <> genInRange t e2
genInRange t e@(Exp _ e1 e2) = [InRange nowhere t e] <> genInRange t e1 <> genInRange t e2
genInRange t e@(IntEnv _ _) = [InRange nowhere t e]
genInRange t e@(Address _ _) = [InRange nowhere t e]
genInRange _ (IntMin _ _)  = error "Internal error: invalid range expression"
genInRange _ (IntMax _ _)  = error "Internal error: invalid range expression"
genInRange _ (UIntMin _ _) = error "Internal error: invalid range expression"
genInRange _ (UIntMax _ _) = error "Internal error: invalid range expression"
genInRange _ (ITE _ _ _ _) = error "Internal error: invalid range expression"

-- | Attempt to construct a `TypedExp` whose type matches the supplied `ValueType`.
-- The target timing parameter will be whatever is required by the caller.
checkExprVType :: forall t. Typeable t => Env -> U.Expr -> ValueType -> Err (TypedExp t)
checkExprVType env e vt@(FromVType typ) = TExp typ (shapeFromVT typ vt) <$> checkExpr env typ (shapeFromVT typ vt) e

showShapedSType :: SType a -> Shape (ActShape a) -> String
showShapedSType (SSArray a) (Shaped l) = show (flattenSType a) <> concatMap (show . singleton) (reverse $ toList l)
showShapedSType a Atomic = show a

typeMismatchErr :: forall a b res. Pn -> SType a -> Shape (ActShape a) -> SType b -> Shape (ActShape b) -> Err res
typeMismatchErr p t1 s1 t2 s2 = (throw (p, "Type " <> showShapedSType t1 s1 <> " should match type " <> showShapedSType t2 s2))

arrayTypeMismatchErr :: forall a b res. Pn -> SType a -> Shape (ActShape a) -> SType b -> Shape (ActShape b) -> Err res
arrayTypeMismatchErr p t1 s1 t2 s2 = (throw (p, "Inconsistent array type: Type " <> showShapedSType t1 s1 <> " should match type " <> showShapedSType t2 s2))

-- | Check if the given expression can be typed with the given type
checkExpr :: forall t a. Typeable t => Env -> SType a -> Shape (ActShape a) -> U.Expr -> Err (Exp a t)
checkExpr env t1 s1 e =
    -- No idea why type annotation is required here
    (inferExpr env e :: Err (TypedExp t)) `bindValidation` (\(TExp t2 s2 te) ->
    maybe (maybeCast (getPosn e) t1 s1 t2 s2 te) (\Refl -> pure te) $ if eqShape s1 s2 then testEquality t1 t2 else Nothing)
    where
      maybeCast :: Pn -> SType a -> Shape (ActShape a) -> SType b -> Shape (ActShape b) -> Exp b t -> Err (Exp a t)
      maybeCast _ SInteger Atomic SContract Atomic te = findContractType env te `bindValidation` (\c -> pure $ Address (fromJust c) te)
      -- maybeCast _ (SSArray _) s1' (SSArray _) s2 _ | s1' == s2 = -- TODO: cast of whole array?
      maybeCast pn t1' s1' t2 s2 _ = typeMismatchErr pn t1' s1' t2 s2

-- | Attempt to infer a type of an expression. If succesfull returns an
-- existential package of the infered typed together with the typed expression.
inferExpr :: forall t. Typeable t => Env -> U.Expr -> Err (TypedExp t)
inferExpr env@Env{calldata, constructors} e = case e of
  -- Boolean expressions
  U.ENot    p v1    -> wrapOp  (Neg  p) Atomic <$> checkExpr env SBoolean Atomic v1
  U.EAnd    p v1 v2 -> wrapOp2 (And  p) Atomic <$> checkExpr env SBoolean Atomic v1 <*> checkExpr env SBoolean Atomic v2
  U.EOr     p v1 v2 -> wrapOp2 (Or   p) Atomic <$> checkExpr env SBoolean Atomic v1 <*> checkExpr env SBoolean Atomic v2
  U.EImpl   p v1 v2 -> wrapOp2 (Impl p) Atomic <$> checkExpr env SBoolean Atomic v1 <*> checkExpr env SBoolean Atomic v2
  U.ELT     p v1 v2 -> wrapOp2 (LT   p) Atomic <$> checkExpr env SInteger Atomic v1 <*> checkExpr env SInteger Atomic v2
  U.ELEQ    p v1 v2 -> wrapOp2 (LEQ  p) Atomic <$> checkExpr env SInteger Atomic v1 <*> checkExpr env SInteger Atomic v2
  U.EGEQ    p v1 v2 -> wrapOp2 (GEQ  p) Atomic <$> checkExpr env SInteger Atomic v1 <*> checkExpr env SInteger Atomic v2
  U.EGT     p v1 v2 -> wrapOp2 (GT   p) Atomic <$> checkExpr env SInteger Atomic v1 <*> checkExpr env SInteger Atomic v2
  U.EEq     p v1 v2 -> TExp SBoolean Atomic <$> polycheck p eqCons v1 v2
  U.ENeq    p v1 v2 -> TExp SBoolean Atomic <$> polycheck p neqCons v1 v2
  U.BoolLit p v1    -> pure $ TExp SBoolean Atomic (LitBool p v1)
  U.EInRange _ abityp v -> TExp SBoolean Atomic . andExps <$> genInRange abityp <$> checkExpr env SInteger Atomic v -- Arithemetic expressions
  U.EAdd   p v1 v2 -> wrapOp2 (Add p) Atomic <$> checkExpr env SInteger Atomic v1 <*> checkExpr env SInteger Atomic v2
  U.ESub   p v1 v2 -> wrapOp2 (Sub p) Atomic <$> checkExpr env SInteger Atomic v1 <*> checkExpr env SInteger Atomic v2
  U.EMul   p v1 v2 -> wrapOp2 (Mul p) Atomic <$> checkExpr env SInteger Atomic v1 <*> checkExpr env SInteger Atomic v2
  U.EDiv   p v1 v2 -> wrapOp2 (Div p) Atomic <$> checkExpr env SInteger Atomic v1 <*> checkExpr env SInteger Atomic v2
  U.EMod   p v1 v2 -> wrapOp2 (Mod p) Atomic <$> checkExpr env SInteger Atomic v1 <*> checkExpr env SInteger Atomic v2
  U.EExp   p v1 v2 -> wrapOp2 (Exp p) Atomic <$> checkExpr env SInteger Atomic v1 <*> checkExpr env SInteger Atomic v2
  U.IntLit p v1    -> pure $ TExp SInteger Atomic (LitInt p v1)

  U.EArray p l -> typedArray `bindValidation` checkAllTypes
    where
      typedArray :: Err [(Pn, TypedExp t)]
      typedArray = traverse (\e' -> (getPosn e',) <$> inferExpr env e') l

      checkAllTypes :: [(Pn, TypedExp t)] -> Err (TypedExp t)
      checkAllTypes tl = case tl of
        (_, TExp styp1 shape1 _ ):_ -> TExp (SSArray styp1) newShape <$> Array p <$> traverse (uncurry (cmpType styp1 shape1)) tl
          where
            newShape = case shape1 of
              Atomic -> Shaped $ NonEmpty.singleton $ length l
              Shaped l' -> Shaped $ (length l) <| l'

            cmpType :: SType a -> Shape (ActShape a) -> Pn -> TypedExp t -> Err (Exp a t)
            cmpType styp shape pn (TExp styp' shape' e') =
              maybe (arrayTypeMismatchErr pn styp shape styp' shape') (\Refl -> pure e') $ if eqShape shape shape' then testEquality styp styp' else Nothing

        [] -> error "Empty array expressions not supported"

    -- Constructor calls
  U.ECreate p c args -> case Map.lookup c constructors of
    Just sig ->
      let ptrs = argContractId <$> sig in
      -- check the types of arguments to constructor call
      checkIxs env p args (fmap castArgType sig) `bindValidation` (\args' ->
      -- then check that all arguments that need to be valid pointers to a contract have a contract type
      traverse_ (uncurry $ checkContractType env) (zip args' ptrs) $>
      TExp SContract Atomic (Create p c args'))
        where
          castArgType :: ArgType -> ValueType
          castArgType (ContractArg _ cid) = ContractType cid
          castArgType (AbiArg at) = PrimitiveType at

          argContractId :: ArgType -> Maybe Id
          argContractId (ContractArg _ cid) = Just cid
          argContractId _ = Nothing

    Nothing -> throw (p, "Unknown constructor " <> show c)

   -- Control
  U.EITE p e1 e2 e3 ->
    checkExpr env SBoolean Atomic e1 `bindValidation` \b ->
    polycheck p (\pn t s te1 te2 -> TExp t s (ITE pn b te1 te2)) e2 e3

  -- Environment variables
  U.EnvExp p v1 -> case lookup v1 globalEnv of
    Just AInteger -> pure $ TExp SInteger Atomic $ IntEnv p v1
    Just AByteStr -> pure $ TExp SByteStr Atomic $ ByEnv  p v1
    _             -> throw (p, "Unknown environment variable " <> show v1)

  -- Variable references
  U.EUTEntry entry | isCalldataEntry entry -> case (eqT @t @Timed, eqT @t @Untimed) of
    (Just Refl, _) -> checkVar Pre entry
    (_, Just Refl) -> checkVar Neither entry
    (_,_) -> error "Internal error: Timing should be either Timed or Untimed"
  U.EPreEntry entry | isCalldataEntry entry  -> error $ "Internal error: Calldata variables cannot be pre" <> show e
  U.EPostEntry entry | isCalldataEntry entry -> error $ "Internal error: Calldata variables cannot be post" <> show e
  -- Storage references
  U.EUTEntry entry   -> checkStorage entry Neither
  U.EPreEntry entry  -> checkStorage entry Pre
  U.EPostEntry entry -> checkStorage entry Post

  _ -> throw (getPosn e, "Internal error: Cannot type expression " <> show e)

  where
    wrapOp f s e1 = TExp sing s (f e1) -- use sign to let Haskell automatically derive the type here
    wrapOp2 f s e1 e2 = TExp sing s (f e1 e2)

    eqCons :: Pn -> SType a -> Shape (ActShape a) -> Exp a t -> Exp a t -> Exp ABoolean t
    eqCons pn SContract _ te1 te2 = Eq pn SInteger (Address (unsafeFindContractType te1) te1) (Address (unsafeFindContractType te2) te2)
    eqCons pn t _ te1 te2 = Eq pn t te1 te2

    neqCons :: Pn -> SType a -> Shape (ActShape a) -> Exp a t -> Exp a t -> Exp ABoolean t
    neqCons pn SContract _ te1 te2 = NEq pn SInteger (Address (unsafeFindContractType te1) te1) (Address (unsafeFindContractType te2) te2)
    neqCons pn t _ te1 te2 = NEq pn t te1 te2

    polycheck :: forall z. Pn -> (forall y. Pn -> SType y -> Shape (ActShape y) -> Exp y t -> Exp y t -> z) -> U.Expr -> U.Expr -> Err z
    polycheck pn cons e1 e2 =
        inferExpr env e1 `bindValidation` \(TExp (t1 :: SType a1) s1 (te1 :: Exp a1 t)) -> -- I don't know why type annotations are required here
        inferExpr env e2 `bindValidation` \(TExp (t2 :: SType a2) s2 (te2 :: Exp a2 t)) ->
        maybe (maybeCast pn cons t1 s1 te1 t2 s2 te2) (\Refl -> pure $ cons pn t1 s1 te1 te2) $ if eqShape s1 s2 then testEquality t1 t2 else Nothing
      where
        maybeCast :: Pn -> (forall y. Pn -> SType y -> Shape (ActShape y) -> Exp y t -> Exp y t -> z)
          -> SType a -> Shape (ActShape a) -> Exp a t
          -> SType b -> Shape (ActShape b) -> Exp b t -> Err z
        maybeCast pn' cons' SInteger Atomic te1 SContract Atomic te2 =
          findContractType env te2 `bindValidation` (\c -> pure $ cons' pn' SInteger Atomic te1 $ Address (fromJust c) te2)
        maybeCast pn' cons' SContract Atomic te1 SInteger Atomic te2 =
          findContractType env te1 `bindValidation` (\c -> pure $ cons' pn' SInteger Atomic (Address (fromJust c) te1) te2)
        -- maybeCast _ (SSArray _) s1' (SSArray _) s2 _ | s1' == s2 = -- TODO: cast of whole array?
        maybeCast pn' _ t1' s1' _ t2 s2 _ = typeMismatchErr pn' t1' s1' t2 s2

    checkVar :: forall t0. Typeable t0 => Time t0 -> U.Entry -> Err (TypedExp t0)
    checkVar whn entry =
        (\(vt@(FromVType typ), ref) -> TExp typ (shapeFromVT typ vt) $ VarRef (getPosEntry entry) whn SCalldata (Item typ vt ref)) <$> (validateEntry env SCalldata entry)

    -- Type check a storage variable
    checkStorage :: forall t0.  Typeable t0 => U.Entry -> Time t0 -> Err (TypedExp t)
    checkStorage entry time =
        -- check that the timing is correct
       checkTime (getPosEntry entry) <*>
       ((\(vt@(FromVType typ), ref) -> TExp typ (shapeFromVT typ vt) $ VarRef (getPosEntry entry) time SStorage (Item typ vt ref)) <$> validateEntry env SStorage entry)

    -- Check that an expression is typed with the right timing
    checkTime :: forall t0. Typeable t0 => Pn -> Err (TypedExp t0 -> TypedExp t)
    checkTime pn = case eqT @t @t0 of
      Just Refl -> pure id
      Nothing   -> throw (pn, (tail . show $ typeRep @t) <> " variable needed here")

    isCalldataEntry (U.EVar _ name) = case Map.lookup name calldata of
      Just _  -> True
      _ -> False
    isCalldataEntry (U.EIndexed _ entry _) = isCalldataEntry entry
    isCalldataEntry (U.EField _ entry _) = isCalldataEntry entry

-- | Helper to create to create a conjunction out of a list of expressions
andExps :: [Exp ABoolean t] -> Exp ABoolean t
andExps [] = LitBool nowhere True
andExps (c:cs) = foldr (And nowhere) c cs

unsafeFindContractType :: Exp a t -> Id
unsafeFindContractType (ITE _ _ a _) =
  unsafeFindContractType a
unsafeFindContractType (Create _ c _) = c
unsafeFindContractType (VarRef _ _ _ (Item _ (ContractType c) _)) = c
unsafeFindContractType _ = error "Internal error: unsafeFindContractType called for non contract expression"

-- | Find the contract id of an expression with contract type
findContractType :: Env -> Exp a t -> Err (Maybe Id)
findContractType env (ITE p _ a b) =
  findContractType env a `bindValidation` \oc1 ->
  findContractType env b `bindValidation` \oc2 ->
  case (oc1, oc2) of
    (Just c1, Just c2) -> Just c1 <$ assert (p, "Type of if-then-else branches does not match") (c1 == c2)
    (_, _ )-> pure Nothing
findContractType _ (Create _ c _) = pure $ Just c
findContractType _ (VarRef _ _ _ (Item _ (ContractType c) _)) = pure $ Just c
findContractType _ _ =  pure Nothing

-- | Check if an expression has the expected contract id, if any
checkContractType :: Env -> TypedExp t -> Maybe Id -> Err ()
checkContractType _ _ Nothing = pure ()
checkContractType env (TExp _ _ e) (Just c) =
  findContractType env e `bindValidation` \case
    Just c' -> assert (posnFromExp e, "Expression was expected to have contract type " <> c <> " but has contract type " <> c') (c == c')
    Nothing -> throw (posnFromExp e, "Expression was expected to have contract type " <> c)

-- | Checks that there are as many expressions as expected by the types,
-- and checks that each one of them agree with its type.
checkIxs :: forall t. Typeable t => Env -> Pn -> [U.Expr] -> [ValueType] -> Err [TypedExp t]
checkIxs env pn exprs types = if length exprs /= length types
                              then throw (pn, "Index mismatch for entry")
                              else traverse (uncurry $ checkExprVType env) (exprs `zip` types)

-- | Checks that there are as many expressions as expected by the array,
-- and checks that each one of them can be typed into Integer
checkArrayIxs :: forall t. Typeable t => Env -> Pn -> [U.Expr] -> [Int] -> Err [(TypedExp t,Int)]
checkArrayIxs env pn exprs ixsBounds = if length exprs > length ixsBounds
                              then throw (pn, "Index mismatch for entry")
                              else traverse check (zip exprs ixsBounds)
  where
    check (e,i) = checkExpr env SInteger Atomic e `bindValidation` (pure . (\e' -> (TExp SInteger Atomic e', i)))
