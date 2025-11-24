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
{-# Language ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}

module Act.Type (typecheck, lookupVars, globalEnv, Err) where

import Prelude hiding (GT, LT)

import EVM.ABI
import Data.Map.Strict    (Map)
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty (toList)
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
                             <* traverse noDuplicateVars [creates | U.Contract (U.Constructor _ _ _ _ _ creates _ _) _ <- contracts]
  where
    store = lookupVars contracts
    constructors = lookupConstructors contracts

    transitions = concatMap (\(U.Contract _ ts) -> ts) contracts

    noDuplicateContracts :: Err ()
    noDuplicateContracts = noDuplicates [(pn,contract) | U.Contract (U.Constructor pn contract _ _ _ _ _ _) _ <- contracts]
                           $ \c -> "Multiple definitions of Contract " <> c

    noDuplicateVars :: U.Creates -> Err ()
    noDuplicateVars (U.Creates assigns) = noDuplicates (fmap fst . fromAssign <$> assigns)
                                          $ \x -> "Multiple definitions of Variable " <> x

    noDuplicateInterfaces :: Err ()
    noDuplicateInterfaces =
      noDuplicates
        [(pn, contract ++ "." ++ (makeIface iface)) | U.Transition pn _ contract iface _ _ _ _ <- transitions]
        $ \c -> "Multiple definitions of Interface " <> c

    noDuplicateBehaviourNames :: Err ()
    noDuplicateBehaviourNames =
      noDuplicates
        [(pn, contract ++ "." ++ behav) | U.Transition pn behav contract _ _ _ _ _ <- transitions]
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
    findCreates c@(Contract (Constructor cname _ _ _ _ _ _) _) = (cname, (createsFromContract c <> pointersFromContract c, c))

--- Finds storage declarations from constructors
lookupVars :: [U.Contract] -> Store
lookupVars = foldMap $ \case
  U.Contract (U.Constructor _ contract _ _ _ (U.Creates assigns) _ _) _ ->
    Map.singleton contract . Map.fromList $ addSlot $ snd . fromAssign <$> assigns
  where
    addSlot :: [(Id, SlotType)] -> [(Id, (SlotType, Integer))]
    addSlot l = zipWith (\(name, typ) slot -> (name, (typ, slot))) l [0..]

-- | A map containing the interfaces of all available constructors together with pointer constraints
type Constructors = Map Id [(AbiType, Maybe Id)]

-- | Construct the constructor map for the given spec
lookupConstructors :: [U.Contract] -> Constructors
lookupConstructors = foldMap $ \case
  U.Contract (U.Constructor _ contract (Interface _ decls) pointers _ _ _ _) _ ->
    let ptrs = Map.fromList $ map (\(PointsTo _ x c) -> (x, c)) pointers in
    Map.singleton contract (map (\(Decl t x) -> (t, Map.lookup x ptrs)) decls)

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
  , calldata     :: Map Id AbiType               -- ^ The calldata var names and their types.
  , pointers     :: Map Id Id                    -- ^ Maps address variables to their contract type.
  , constructors :: Constructors                 -- ^ Interfaces of constructors
  }
  deriving (Show)

-- | Environment with globally available variables.
globalEnv :: [(EthEnv, TValueType AInteger)]
globalEnv =
  [(Callvalue, TInteger 256 Unsigned),
   (Caller, TAddress),
   (Blockhash, TInteger 256 Unsigned),
   (Blocknumber, TInteger 256 Unsigned),
   (Difficulty, TInteger 256 Unsigned),
   (Timestamp, TInteger 256 Unsigned),
   (Gaslimit, TInteger 256 Unsigned),
   (Coinbase, TAddress),
   (Chainid, TInteger 256 Unsigned),
   (This, TAddress),
   (Origin, TAddress),
   (Nonce, TInteger 256 Unsigned),
   (Calldepth, TInteger 80 Unsigned)
  ]


mkEnv :: Id -> Store -> Constructors -> Env
mkEnv contract store constructors = Env
  { contract = contract
  , store    = Map.map fst $ fromMaybe mempty (Map.lookup contract store)
  , theirs   = store
  , calldata = mempty
  , pointers = mempty
  , constructors = constructors
  }

-- Add calldata to environment
addCalldata :: [Decl] -> Env -> Env
addCalldata decls env = env{ calldata = abiVars }
  where
   abiVars = Map.fromList $ map (\(Decl typ var) -> (var, typ)) decls

-- Add pointers to environment
addPointers :: [Pointer] -> Env -> Env
addPointers decls env = env{ pointers = ptrs }
  where
   ptrs = Map.fromList $ map (\(PointsTo _ x c) -> (x, c)) decls

-- Type check a contract
checkContract :: Store -> Constructors -> U.Contract -> Err Contract
checkContract store constructors (U.Contract constr@(U.Constructor _ cid _ _ _ _ _ _) trans) =
  Contract <$> checkConstructor env constr <*> (concat <$> traverse (checkBehavior env) trans) <* namesConsistent
  where
    env :: Env
    env = mkEnv cid store constructors

    namesConsistent :: Err ()
    namesConsistent =
      traverse_ (\(U.Transition pn _ cid' _ _ _ _ _) -> assert (errmsg pn cid') (cid == cid')) trans

    errmsg pn cid' = (pn, "Behavior must belong to contract " <> show cid <> " but belongs to contract " <> cid')


-- Type check a behavior
checkBehavior :: Env -> U.Transition -> Err [Behaviour]
checkBehavior env (U.Transition _ name contract iface@(Interface _ decls) ptrs iffs cases posts) =
  traverse (checkPointer env') ptrs *>
  noIllegalWilds *>
  -- constrain integer calldata variables (TODO: other types)
  fmap fmap (makeBehv <$> checkIffs env' iffs <*> traverse (checkExpr env' TBoolean) posts)
  <*> traverse (checkCase env') normalizedCases
  where
    -- Add calldata variables and pointers to the typing environment
    env' = addPointers ptrs $ addCalldata decls env

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
    makeBehv pres posts' (casecond,storage,ret) = Behaviour name contract iface ptrs pres casecond posts' storage ret

checkConstructor :: Env -> U.Constructor -> Err Constructor
checkConstructor env (U.Constructor _ contract (Interface _ decls) ptrs iffs (U.Creates assigns) postcs invs) =
  do
    traverse_ (checkPointer env') ptrs
    stateUpdates <- concat <$> traverse (checkAssign env') assigns
    iffs' <- checkIffs envNoStorage iffs
    traverse_ (validStorage env') assigns
    ensures :: [Exp a Untimed] <- traverse (checkExpr env' TBoolean) postcs
    invs' <- fmap (Invariant contract [] [] . PredUntimed) <$> traverse (checkExpr env' TBoolean) invs
    pure $ Constructor contract (Interface contract decls) ptrs iffs' ensures invs' stateUpdates
  where
    env' = addPointers ptrs $ addCalldata decls env
    -- type checking environment prior to storage creation of this contract
    envNoStorage = env'{ store = mempty }

-- | Checks that a pointer declaration x |-> A is valid. This consists of
-- checking that x is a calldata variable that has address type and A is a valid
-- contract type.
checkPointer :: Env -> U.Pointer -> Err ()
checkPointer Env{theirs,calldata} (U.PointsTo p x c) =
  maybe (throw (p, "Contract " <> c <> " is not a valid contract type")) (\_ -> pure ()) (Map.lookup c theirs) *>
  case Map.lookup x calldata of
    Just AbiAddressType -> pure ()
    Just  _ -> throw (p, "Variable " <> x <> " does not have an address type")
    Nothing -> throw (p, "Unknown variable " <> x)


-- | Check if the types of storage variables are valid
validStorage :: Env -> U.Assign -> Err ()
validStorage env (U.AssignVal (U.StorageVar p t _) _) = validSlotType env p t
validStorage env (U.AssignMapping (U.StorageVar p t _) _) = validSlotType env p t

-- | Check if the a contract type is valid in an environment
validType :: Env -> Pn -> ValueType -> Err ()
validType Env{theirs} p (ValueType (TContract c)) =
  maybe (throw (p, "Contract " <> c <> " is not a valid contract type")) (\_ -> pure ()) $ Map.lookup c theirs
validType _ _ _ = pure ()

validKey :: Pn -> ValueType -> Err ()
validKey p (ValueType (TContract _)) = throw (p, "Mappings cannot have contract indices")
validKey _ _ = pure ()

validSlotType :: Env -> Pn -> SlotType -> Err ()
validSlotType env p (StorageMapping ks res) = traverse_ (\k -> validType env p k <* validKey p k) ks <* validType env p res
validSlotType env p (StorageValue t) = validType env p t


-- | Type checks a case, returning typed versions of its preconditions, rewrites and return value.
checkCase :: Env -> U.Case -> Err ([Exp ABoolean Untimed], [StorageUpdate], Maybe (TypedExp Timed))
checkCase env c@(U.Case _ pre post) = do
  -- TODO isWild checks for WildExp, but WildExp is never generated
  if' <- traverse (checkExpr env TBoolean) $ if isWild c then [U.BoolLit nowhere True] else [pre]
  (storage,return') <- checkPost env post
  pure (if',storage,return')

-- Check the initial assignment of a storage variable
checkAssign :: Env -> U.Assign -> Err [StorageUpdate]
checkAssign env@Env{contract} (U.AssignVal (U.StorageVar pn (StorageValue (ValueType vt)) name) expr)
  = sequenceA [checkExpr envNoStorage vt expr `bindValidation` \te ->
              -- TODO: Check if this is sufficient. Since contract type should now be checked
              -- by `checkExpr`, there should be no need for `{find,valid}ContractType`
               --findContractType env te `bindValidation` \ctyp ->
               pure $ _Update (Item vt (SVar pn contract name)) te ] -- <$ validContractType pn (ValueType vt) ctyp]
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
checkDefn pn env@Env{contract} keyType (ValueType vt) name (U.Mapping k val) =
  _Update
  <$> (Item vt . SMapping nowhere (SVar pn contract name) (ValueType vt) <$> checkIxs env (getPosn k) [k] [keyType])
  <*> checkExpr env vt val

-- | Type checks a postcondition, returning typed versions of its storage updates and return expression.
checkPost :: Env -> U.Post -> Err ([StorageUpdate], Maybe (TypedExp Timed))
checkPost env (U.Post storage maybeReturn) = do
  returnexp <- traverse (inferExpr env) maybeReturn
  storage' <- checkEntries storage
  pure (storage', returnexp)
  where
    checkEntries :: [U.Storage] -> Err [StorageUpdate]
    checkEntries entries = for entries $ \case
      U.Update loc val -> checkStorageExpr env loc val

checkEntry :: forall t k. Typeable t => Env -> SRefKind k -> U.Entry -> Err (SlotType, Maybe Id, Ref k t)
checkEntry Env{contract,store,calldata,pointers} kind (U.EVar p name) = case (kind, Map.lookup name store, Map.lookup name calldata) of
  -- Note: Inconsistency between the `kind` and the environments should not actually happen, since the
  -- `kind` parameter gets its value in `inferExpr` by lookup in the environment itself (see `isCalldataEntry`).
  -- `kind`'s presence helps with the typing of `k`, but maybe we can rewrite to avoid unnecessary cases..
  (_, Just _, Just _) -> throw (p, "Ambiguous variable " <> name)
  (SStorage, Just typ@(StorageValue (ValueType (TContract c))), Nothing) -> pure (typ, Just c, SVar p contract name)
  (SStorage, Just typ, Nothing) -> pure (typ, Nothing, SVar p contract name)
  (SCalldata, Nothing, Just typ) -> pure (StorageValue (fromAbiType' typ), Map.lookup name pointers, CVar p typ name)
  (SStorage, _, Just _) -> error "Internal error: Expected storage variable but found calldata variable"
  (SCalldata, Just _, _) -> error "Internal error: Expected calldata variable but found storage variable"
  (_, Nothing, Nothing) -> throw (p, "Unknown variable " <> show name)
checkEntry env kind (U.EIndexed p e args) =
  checkEntry env kind e `bindValidation` \(styp, _, ref) -> case styp of
    StorageValue vt@(ValueType t) -> case flattenValueType t of
      (_, Nothing) -> throw (p, "Expression should have a mapping or array type" <> show e)
      (_, Just sizes) ->
        checkArrayIxs env p args (toList sizes) `bindValidation` \ixs ->
        pure (StorageValue (derefValueType (length ixs) vt), Nothing, SArray p ref (derefValueType (length ixs) vt) ixs)
        where
          derefValueType :: Int -> ValueType -> ValueType
          derefValueType n (ValueType (TArray _ t')) | n > 0 = derefValueType (n-1) (ValueType t')
          derefValueType _ t' = t'
    StorageMapping argtyps restyp ->
        (StorageValue restyp, Nothing,) . SMapping p ref restyp <$> checkIxs env p args (NonEmpty.toList argtyps)
checkEntry env@Env{theirs} kind (U.EField p e x) =
  checkEntry env kind e `bindValidation` \(_, oc, ref) -> case oc of
    Just c -> case Map.lookup c theirs of
      Just cenv -> case Map.lookup x cenv of
        Just (st@(StorageValue (ValueType (TContract c'))), _) -> pure (st, Just c', SField p ref c x)
        Just (st, _) -> pure (st, Nothing, SField p ref c x)
        Nothing -> throw (p, "Contract " <> c <> " does not have field " <> x)
      Nothing -> error $ "Internal error: Invalid contract type " <> show c
    _ -> throw (p, "Expression should have a contract type" <> show e)

validateEntry :: forall t k. Typeable t => Env -> SRefKind k -> U.Entry -> Err (ValueType, Ref k t)
validateEntry env kind entry =
  checkEntry env kind entry `bindValidation` \(typ, oc, ref) -> case typ of
    StorageValue t -> case oc of
                        Just cid -> pure (ValueType (TContract cid), ref)
                        _ -> pure (t, ref)
    StorageMapping _ _  -> throw (getPosEntry entry, "Top-level expressions cannot have mapping type")

-- | Typecheck a storage update
checkStorageExpr :: Env -> U.Entry -> U.Expr -> Err StorageUpdate
checkStorageExpr env entry expr =
  validateEntry env SStorage entry `bindValidation` \(ValueType vt, ref) ->
  checkExpr env vt expr `bindValidation` \te ->
  --findContractType env te `bindValidation` \ctyp ->
  pure $ _Update (Item vt ref) te -- <$ validContractType (getPosn expr) (ValueType vt) ctyp


validContractType :: Pn -> ValueType -> Maybe Id -> Err ()
validContractType pn (ValueType (TContract c1)) (Just c2) =
  assert (pn, "Assignment to storage variable was expected to have contract type " <> c1 <> " but has contract type " <> c2) (c1 == c2)
validContractType pn (ValueType (TContract c1)) Nothing =
  throw (pn, "Assignment to storage variable was expected to have contract type " <> c1)
validContractType _ _ _ = pure ()

checkIffs :: Env -> U.Iff -> Err [Exp ABoolean Untimed]
checkIffs env exps = traverse (checkExpr env TBoolean) exps

-- | If an `inrange e` predicate appears in the source code, then the inrange
-- predicate is propagated to all subexpressions of `e`. This elaboration step
-- happens here.
genInRange :: TValueType AInteger -> Exp AInteger t -> [Exp ABoolean t]
genInRange t e@(LitInt _ _) = [InRange nowhere t e]
genInRange t e@(VarRef _ _ _ _)  = [InRange nowhere t e]
genInRange t e@(Add _ e1 e2) = [InRange nowhere t e] <> genInRange t e1 <> genInRange t e2
genInRange t e@(Sub _ e1 e2) = [InRange nowhere t e] <> genInRange t e1 <> genInRange t e2
genInRange t e@(Mul _ e1 e2) = [InRange nowhere t e] <> genInRange t e1 <> genInRange t e2
genInRange t e@(Div _ e1 e2) = [InRange nowhere t e] <> genInRange t e1 <> genInRange t e2
genInRange t e@(Mod _ e1 e2) = [InRange nowhere t e] <> genInRange t e1 <> genInRange t e2
genInRange t e@(Exp _ e1 e2) = [InRange nowhere t e] <> genInRange t e1 <> genInRange t e2
genInRange t e@(IntEnv _ _) = [InRange nowhere t e]
--genInRange _ (Create _ _ _) = []
genInRange _ (IntMin _ _)  = error "Internal error: invalid range expression"
genInRange _ (IntMax _ _)  = error "Internal error: invalid range expression"
genInRange _ (UIntMin _ _) = error "Internal error: invalid range expression"
genInRange _ (UIntMax _ _) = error "Internal error: invalid range expression"
genInRange _ (ITE _ _ _ _) = error "Internal error: invalid range expression"

-- | Attempt to construct a `TypedExp` whose type matches the supplied `ValueType`.
-- The target timing parameter will be whatever is required by the caller.
checkExprVType :: forall t. Typeable t => Env -> U.Expr -> ValueType -> Err (TypedExp t)
checkExprVType env e (ValueType vt) = TExp vt <$> checkExpr env vt e

--showShapedSType :: SType a -> Shape (ActShape a) -> String
--showShapedSType (SSArray a) (Shaped l) = show (flattenSType a) <> concatMap (show . singleton) (reverse $ toList l)
--showShapedSType a _ = show a

typeMismatchErr :: forall a b res. Pn -> TValueType a -> TValueType b -> Err res
typeMismatchErr p t1 t2 = (throw (p, "Type " <> show t1 <> " should match type " <> show t2))

arrayTypeMismatchErr :: forall a b res. Pn -> TValueType a -> TValueType b -> Err res
arrayTypeMismatchErr p t1 t2 = (throw (p, "Inconsistent array type: Type " <> show t1 <> " should match type " <> show t2))

defaultInteger :: TValueType AInteger
defaultInteger = TInteger 256 Signed

defaultUInteger :: TValueType AInteger
defaultUInteger = TInteger 256 Unsigned

relaxedIntCheck :: TValueType a -> TValueType b -> Maybe (a :~: b)
relaxedIntCheck (TInteger _ _) (TInteger _ _) = Just Refl
relaxedIntCheck (TArray n1 t1) (TArray n2 t2) | n1 == n2 = (\Refl -> Just Refl) =<< relaxedIntCheck t1 t2
relaxedIntCheck t1 t2 = testEquality t1 t2

-- | Check if the given expression can be typed with the given type
checkExpr :: forall t a. Typeable t => Env -> TValueType a -> U.Expr -> Err (Exp a t)
checkExpr env t1 e =
    -- No idea why type annotation is required here
    (inferExpr env e :: Err (TypedExp t)) `bindValidation` (\(TExp t2 te) ->
    -- TODO: when integer types will always be infered to be `defaultInteger`, so mismatch is
    -- certain for any other type. Implement conversion, and probably check validity through SMT
    -- under the preconditions/case conditions?
    maybe (typeMismatchErr (getPosn e) t1 t2) (\Refl -> pure te) $ relaxedIntCheck t1 t2)

-- | Attempt to infer a type of an expression. If succesfull returns an
-- existential package of the infered typed together with the typed expression.
inferExpr :: forall t. Typeable t => Env -> U.Expr -> Err (TypedExp t)
inferExpr env@Env{calldata, constructors} e = case e of
  -- Boolean expressions
  U.ENot    p v1    -> wrapOp  (Neg  p) TBoolean <$> checkExpr env TBoolean v1
  U.EAnd    p v1 v2 -> boolOp2 (And  p) TBoolean v1 v2
  U.EOr     p v1 v2 -> boolOp2 (Or   p) TBoolean v1 v2
  U.EImpl   p v1 v2 -> boolOp2 (Impl p) TBoolean v1 v2
  U.ELT     p v1 v2 -> boolOp2 (LT   p) defaultInteger v1 v2
  U.ELEQ    p v1 v2 -> boolOp2 (LEQ  p) defaultInteger v1 v2
  U.EGEQ    p v1 v2 -> boolOp2 (GEQ  p) defaultInteger v1 v2
  U.EGT     p v1 v2 -> boolOp2 (GT   p) defaultInteger v1 v2
  U.EEq     p v1 v2 -> TExp TBoolean <$> polycheck p Eq v1 v2
  U.ENeq    p v1 v2 -> TExp TBoolean <$> polycheck p NEq v1 v2
  U.BoolLit p v1    -> pure $ TExp TBoolean (LitBool p v1)
  U.EInRange _ (fromAbiType' -> ValueType TAddress) v -> TExp TBoolean . andExps <$> genInRange TAddress <$> checkExpr env TAddress v -- Arithemetic expressions
  U.EInRange _ (fromAbiType' -> ValueType t@(TInteger _ _)) v -> TExp TBoolean . andExps <$> genInRange t <$> checkExpr env t v
  U.EAdd   p v1 v2 -> arithOp2 (Add p) v1 v2
  U.ESub   p v1 v2 -> arithOp2 (Sub p) v1 v2
  U.EMul   p v1 v2 -> arithOp2 (Mul p) v1 v2
  U.EDiv   p v1 v2 -> arithOp2 (Div p) v1 v2
  U.EMod   p v1 v2 -> arithOp2 (Mod p) v1 v2
  U.EExp   p v1 v2 -> arithOp2 (Exp p) v1 v2
  U.IntLit p v1    -> pure $ TExp (TInteger 256 Signed) (LitInt p v1)

  U.EArray p l -> typedArray `bindValidation` checkAllTypes
    where
      typedArray :: Err [(Pn, TypedExp t)]
      typedArray = traverse (\e' -> (getPosn e',) <$> inferExpr env e') l

      checkAllTypes :: [(Pn, TypedExp t)] -> Err (TypedExp t)
      checkAllTypes tl = case tl of
        (_, TExp styp1 _ ):_ -> TExp newType <$> Array p <$> traverse (uncurry (cmpType styp1)) tl
          where
            --newShape = case shape1 of
            --  Atomic -> Shaped $ NonEmpty.singleton $ length l
            --  Shaped l' -> Shaped $ (length l) <| l'

            newType = TArray (length l) styp1
              --TArray n t -> TArray (length l : n) t

            cmpType :: TValueType a -> Pn -> TypedExp t -> Err (Exp a t)
            cmpType styp pn (TExp styp' e') =
              maybe (arrayTypeMismatchErr pn styp styp') (\Refl -> pure e') $ relaxedIntCheck styp styp' --if eqShape shape shape' then testEquality styp styp' else Nothing

        [] -> error "Empty array expressions not supported"

    -- Constructor calls
  U.ECreate p c args -> case Map.lookup c constructors of
    Just sig ->
      let (typs, ptrs) = unzip sig in
      -- check the types of arguments to constructor call
      checkIxs env p args (fmap fromAbiType' typs) `bindValidation` (\args' ->
      -- then check that all arguments that need to be valid pointers to a contract have a contract type
      traverse_ (uncurry $ checkContractType env) (zip args' ptrs) $>
      TExp (TContract c) (Create p c args')) --TODO: change integer type maybe?
    Nothing -> throw (p, "Unknown constructor " <> show c)

   -- Control
  U.EITE p e1 e2 e3 ->
    checkExpr env TBoolean e1 `bindValidation` \b ->
    polycheck p (\pn t te1 te2 -> TExp t (ITE pn b te1 te2)) e2 e3

  -- Environment variables
  U.EnvExp p v1 -> case lookup v1 globalEnv of
    Just t -> pure $ TExp t $ IntEnv p v1 -- TODO: is Unsigned True?
    --Just t -> pure $ TExp t $ ByEnv  p v1
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
    wrapOp f t e1 = TExp t (f e1) -- use sign to let Haskell automatically derive the type here
    --wrapOp2 f t e1 e2 = TExp t (f e1 e2)

    boolOp2 :: forall a. (Exp a t -> Exp a t -> Exp ABoolean t) -> TValueType a -> U.Expr -> U.Expr -> Err (TypedExp t)
    boolOp2 f t e1 e2 = do
      e1' <- checkExpr env t e1
      e2' <- checkExpr env t e2
      pure $ TExp TBoolean (f e1' e2')

    arithOp2 :: (Exp AInteger t -> Exp AInteger t -> Exp AInteger t) -> U.Expr -> U.Expr -> Err (TypedExp t)
    arithOp2 f e1 e2 = do
      e1' <- checkExpr env defaultInteger e1
      e2' <- checkExpr env defaultInteger e2
      pure $ TExp defaultInteger (f e1' e2')


    polycheck :: forall z. Pn -> (forall y. ActSingI y => Pn -> TValueType y -> Exp y t -> Exp y t -> z) -> U.Expr -> U.Expr -> Err z
    polycheck pn cons e1 e2 =
        inferExpr env e1 `bindValidation` \(TExp (t1 :: TValueType a1) (te1 :: Exp a1 t)) -> -- I don't know why type annotations are required here
        inferExpr env e2 `bindValidation` \(TExp (t2 :: TValueType a2) (te2 :: Exp a2 t)) ->
        maybe (typeMismatchErr pn t1 t2) (\Refl -> pure $ cons pn t1 te1 te2) $ relaxedIntCheck t1 t2

    checkVar :: forall t0. Typeable t0 => Time t0 -> U.Entry -> Err (TypedExp t0)
    checkVar whn entry =
        (\(ValueType vt, ref) -> TExp vt $ VarRef (getPosEntry entry) whn SCalldata (Item vt ref)) <$> (validateEntry env SCalldata entry)

    -- Type check a storage variable
    checkStorage :: forall t0.  Typeable t0 => U.Entry -> Time t0 -> Err (TypedExp t)
    checkStorage entry time =
        -- check that the timing is correct
       checkTime (getPosEntry entry) <*>
       ((\(ValueType vt, ref) -> TExp vt $ VarRef (getPosEntry entry) time SStorage (Item vt ref)) <$> validateEntry env SStorage entry)

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


-- | Find the contract id of an expression with contract type
findContractType :: Env -> Exp a t -> Err (Maybe Id)
findContractType env (ITE p _ a b) =
  findContractType env a `bindValidation` \oc1 ->
  findContractType env b `bindValidation` \oc2 ->
  case (oc1, oc2) of
    (Just c1, Just c2) -> Just c1 <$ assert (p, "Type of if-then-else branches does not match") (c1 == c2)
    (_, _ )-> pure Nothing
findContractType _ (Create _ c _) = pure $ Just c
findContractType _ (VarRef _ _ _ (Item (TContract c) _)) = pure $ Just c
findContractType _ _ =  pure Nothing

-- | Check if an expression has the expected contract id, if any
checkContractType :: Env -> TypedExp t -> Maybe Id -> Err ()
checkContractType _ _ Nothing = pure ()
checkContractType env (TExp _ e) (Just c) =
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
    check (e,i) = checkExpr env defaultUInteger e `bindValidation` (pure . (\e' -> (TExp defaultUInteger e', i)))
