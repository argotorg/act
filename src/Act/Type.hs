{-# Language GADTs #-}
{-# Language RankNTypes #-}
{-# Language ScopedTypeVariables #-}
{-# Language NamedFieldPuns #-}
{-# Language DataKinds #-}
{-# Language KindSignatures #-}
{-# Language ApplicativeDo #-}
{-# Language ViewPatterns #-}
{-# Language TypeOperators #-}
{-# Language InstanceSigs #-}
{-# Language TupleSections #-}

module Act.Type (typecheck, Err, Constraint(..), Env(..), Constructors) where

import Prelude hiding (GT, LT)
import Data.Map.Strict    (Map)
import Data.Bifunctor (first)
import Data.Maybe
import qualified Data.Map.Strict    as Map
import Data.Typeable ((:~:)(Refl))
import Data.Type.Equality (TestEquality(..))
import Control.Monad (unless)
import Data.Foldable

import Act.Syntax
import Act.Syntax.Timing
import Act.Syntax.Untyped qualified as U
import Act.Syntax.TypedImplicit
import Act.Error
import Act.Print
import Act.Bounds


type Err = Error String

-- | A map containing the interfaces of all available constructors, a payable flag, and the constructor preconditions.
type Constructors = Map Id Constructor

-- | The type checking environment.
data Env = Env
  { contract     :: Id                           -- ^ The name of the current contract.
  , storage      :: StorageTyping                -- ^ StorageTyping
  , calldata     :: Map Id ArgType               -- ^ The calldata var names and their types.
  , constructors :: Constructors                 -- ^ Interfaces and preconditions of constructors
  , preconds     :: [Exp ABoolean Untimed]       -- ^ Constraint context
  }
  deriving (Show, Eq)

emptyEnv :: Env
emptyEnv = Env
  { contract     = ""
  , storage      = mempty
  , calldata     = mempty
  , constructors = mempty
  , preconds     = []
  }

-- | Functions to manipulate environments

-- Add the name of the current contract to the environment
addContractName :: Id -> Env -> Env
addContractName cid env = env{ contract = cid }

-- Add calldata arguments of the current constructor/transition to the environment
addCalldata :: [Arg] -> Env -> Env
addCalldata decls env = env{ calldata = abiVars }
  where
   abiVars = Map.fromList $ map (\(Arg typ var) -> (var, typ)) decls

-- Add storage typing of a contract to the environment
addConstrStorage :: Id -> Map Id (ValueType, Integer) -> Env -> Env
addConstrStorage cid storageTyping env =
    env { storage = Map.insert cid storageTyping (storage env) }

-- Add the whole constructor to the environment. This is needed to typecheck
-- constructor calls and also later on, to perform the entailment checking.
addConstructor :: Id -> Constructor -> Env -> Env
addConstructor cid cnstr env =
  env { constructors = Map.insert cid cnstr (constructors env) }

-- Add constructor preconditions to the environment
addPreconds :: [Exp ABoolean Untimed] -> Env -> Env
addPreconds pres env =
  env { preconds = pres <> preconds env }

-- Clear local environment (calldata and preconditions)
clearLocalEnv :: Env -> Env
clearLocalEnv env =
  env { calldata = mempty, preconds = mempty }

-- | Constraints generated during type checking.
-- An integer constraint constrains an integer expression to fit within the bounds of a given type.
-- A call constraint constrains the arguments of a constructor call to satisfy the constructor's preconditions.
data Constraint t =
    BoolCnstr Pn String Env (Exp ABoolean t) -- ^ Boolean constraint with a message, environment, and boolean expression. Generated to check integer bounds, case consistency, and array bounds.
  | CallCnstr Pn String Env [TypedExp t] Id  -- ^ Call constraint with a message, environment, argument list, and constructor id. Generated to check that preconditions of the called constructor are satisfied.
    deriving (Show, Eq)

instance Annotatable Constraint where
  annotate :: Constraint Untimed -> Constraint Timed
  annotate (BoolCnstr p msg env e) = BoolCnstr p msg env (setPre e)
  annotate (CallCnstr p msg env es i) = CallCnstr p msg env (setPre <$> es) i


-- | Create an integer bound constraint
makeIntegerBoundConstraint :: Pn -> String -> Env -> TValueType AInteger -> Exp AInteger t -> Constraint t
makeIntegerBoundConstraint p str env t e = BoolCnstr p str env (InRange nowhere t e)

-- | Create an array bound constraint
makeArrayBoundConstraint :: Pn -> String -> Env -> Int -> Exp AInteger t -> Constraint t
makeArrayBoundConstraint p str env len e = BoolCnstr p str env (LT p e (LitInt p (fromIntegral len)))

-- | Top-level typechecking function
typecheck :: U.Act -> Err (Act, [Constraint Timed])
typecheck (U.Main contracts) = do
    (\(storageTyping, tcontracts, cnstrs) -> (Act storageTyping tcontracts, annotate <$> cnstrs)) <$> checkContracts' contracts

checkContracts' :: [U.Contract] -> Err (StorageTyping, [Contract], [Constraint Untimed])
checkContracts' cs = (\(s, tcs, cnstrs) -> (storage s, tcs, cnstrs)) <$> checkContracts emptyEnv cs

-- | Typecheck a list of contracts
checkContracts :: Env -> [U.Contract] -> Err (Env, [Contract], [Constraint Untimed])
checkContracts env [] = pure (env, [], [])
checkContracts env ((U.Contract p cid cnstr behvs):cs) =
    -- Check that the constructor name is not already defined
    checkContrName cid env *>
    -- Add contract name to environment
    let env' = addContractName cid env in
    -- Check constructor
    checkConstructor env' cnstr `bindValidation` \(constr', env'', cnstrs1) -> do
    -- Check behaviors
    behvsc <- checkBehaviours env'' behvs
    -- Check remaining contracts
    (env''', cs', cnstrs3) <- checkContracts env'' cs
    pure $ let (behvs', cnstrs2) = behvsc in
           (env''', Contract constr' behvs' : cs', cnstrs1 ++ cnstrs2 ++ cnstrs3)

    where
        checkContrName :: Id -> Env -> Err ()
        checkContrName cid' Env{constructors} =
            case Map.lookup cid' constructors of
                Just _ -> throw (p, "Constructor " <> cid' <> " is already defined")
                Nothing -> pure ()

-- | Typecheck a constructor
checkConstructor :: Env -> U.Constructor -> Err (Constructor, Env, [Constraint Untimed])
checkConstructor env (U.Constructor _ (Interface p params) payable iffs cases posts _) =
    -- find constructor name
    let cid = contract env
    -- add parameters to environment
        env' = addCalldata params env in
    -- check that parameter types are valid
    traverse_ (checkParams env) params *>
    -- check preconditions
    (unzip <$> traverse (checkExpr env' U TBoolean) iffs) `bindValidation` \(iffs1, cnstr1) ->
    -- add implicit CALLVALUE == 0 precondition if not payable
    let iffs' = addCallvalueZeroPrecond payable iffs1 in
    -- check postconditions
    let env'' = addPreconds iffs' env' in
    (checkConstrCases env'' cases) `bindValidation` \(storageType, cases', cnstr2) -> do
    -- construct the new environment
    let env''' = addConstrStorage cid storageType env''
    -- check case consistency
    let casecnstrs = checkCaseConsistency env' cases'
    -- check postconditions
    ensures <- map fst <$> traverse (checkExpr env''' U TBoolean) posts
    -- Note: ivariants are ignored for the time being and not checked
    pure $ -- add integer bounds for calldata and (used) storage variables
           let bounds = boundsConstructor (Constructor cid (Interface p params) payable iffs' cases' ensures [])
               constr = Constructor cid (Interface p params) payable (iffs' <> bounds) cases' ensures []
               -- add the constructor to the environment
               env'''' = addConstructor cid constr env'''
               -- capture the preconditions that include the added bounds
               cnstrs = addIffs bounds $ concat cnstr1 ++ cnstr2 ++ casecnstrs
           in
            -- return the constructor and the new environment
            (constr, clearLocalEnv env'''', cnstrs)


-- | Extend a list of constraints with additional preconditions. Useful for adding integer bounds.
addIffs :: [Exp ABoolean Untimed] -> [Constraint Untimed] -> [Constraint Untimed]
addIffs iffs cnstrs = addIff <$> cnstrs
  where
    addIff :: Constraint Untimed -> Constraint Untimed
    addIff (BoolCnstr p msg env e) =
        BoolCnstr p msg (addPreconds iffs env) e
    addIff (CallCnstr p msg env args cid) =
        CallCnstr p msg (addPreconds iffs env) args cid

-- | Check that constructor/transition parameters have valid types
checkParams :: Env -> U.Arg -> Err ()
checkParams Env{storage} (Arg (ContractArg p c) _) =
  case Map.lookup c storage of
    Nothing -> throw (p, "Contract " <> c <> " is not a valid contract type")
    Just _ -> pure ()
-- TODO check that abi types are valid
checkParams _ _ = pure ()

-- | Type check each case of a constructor
checkConstrCases :: Env -> [U.Case U.Creates]
                 -> Err (Map Id (ValueType, Integer), Cases [StorageUpdate], [Constraint Untimed])
checkConstrCases env cases = do
  -- check each case separately
  checkCases cases `bindValidation` \(cases', cnstr) -> do
    -- then construct storage typing and check consistency
    storageTyping <- checkStorageTyping cases
    pure (storageTyping, cases', cnstr)
  where
    checkCases :: [U.Case U.Creates] -> Err (Cases [StorageUpdate], [Constraint Untimed])
    checkCases [] = pure ([], [])
    checkCases ((U.Case p cond assigns):cs) =
        -- check case condition
        checkExpr env U TBoolean cond `bindValidation` \(ccond, cnstr1) -> do
        -- add case condition to environment preconditions
        let env' = addPreconds [ccond] env
        -- check assignments
        r2 <- unzip <$> traverse (checkAssign env') assigns
        -- check remaining cases
        r3 <- checkCases cs
        -- because we use applicative-do we need to do deconstruct tuples inside pure
        pure $ let (cases', cnstr3) = r3 in
               let (updates, cnstr2) = r2 in
               ((Case p ccond updates):cases', cnstr1 ++ concat cnstr2 ++ cnstr3)

    -- check that storage typing is consistent across all cases
    checkStorageTyping :: [U.Case U.Creates] -> Err (Map Id (ValueType, Integer))
    checkStorageTyping [] = pure mempty
    checkStorageTyping ((U.Case _ _ assigns):_) = do
        let typing = makeStorageTyping assigns 0
        consistentStorageTyping typing cases
        noDuplicates assigns
        pure $ Map.fromList typing

    -- check that there are no duplicate storage variables in a case
    noDuplicates :: [U.Assign] -> Err ()
    noDuplicates [] = pure ()
    noDuplicates ((U.StorageVar p _ name, _):rest) =
        (assert (p, "Duplicate storage variable " <> show name) (not (any (\(U.StorageVar _ _ n, _) -> n == name) rest))) *>
        noDuplicates rest

    -- make the storage typing from a list of assignments
    makeStorageTyping :: [U.Assign] -> Integer ->  [(Id, (ValueType, Integer))]
    makeStorageTyping [] _ = []
    makeStorageTyping ((U.StorageVar _ typ name, _):rest) slot = (name, (typ, slot)):makeStorageTyping rest (slot + 1)

    -- check that the storage typing is the same across all cases
    consistentStorageTyping :: [(Id, (ValueType, Integer))] -> [U.Case U.Creates] -> Err ()
    consistentStorageTyping _ [] = pure ()
    consistentStorageTyping typing ((U.Case p _ assigns):cases') =
        let typing' = makeStorageTyping assigns 0 in
        consistentStorageTyping typing cases' *>
        assert (p, "Inconsistent storage typing in constructor cases") (typing == typing')


-- | Type check a list of transitions
checkBehaviours :: Env -> [U.Transition] -> Err ([Behaviour], [Constraint Untimed])
checkBehaviours _ [] = pure ([], [])
checkBehaviours env (b:bhs) = do
    -- check that there are no duplicate transition names
    checkBehvName b bhs
    -- check individual transition
    b' <- checkBehaviour env b
    -- check remaining transitions
    bs' <- checkBehaviours env bhs
    pure $ let (tbehv, bcnstrs) = b'
               (tbs, bscnstrs) = bs' in
            (tbehv:tbs, bcnstrs ++ bscnstrs)

    where
        checkBehvName :: U.Transition -> [U.Transition] -> Err ()
        checkBehvName (U.Transition pn name _ _ _ _ _ _) bhs' =
            case find (\(U.Transition _ n _ _ _ _ _ _) -> n == name) bhs' of
                Just _ -> throw (pn, "Behaviour " <> name <> "for contract " <> contract env <> " is already defined")
                Nothing -> pure ()

-- | Type check a single transition
checkBehaviour :: Env -> U.Transition -> Err (Behaviour, [Constraint Untimed])
checkBehaviour env@Env{contract} (U.Transition _ name iface@(Interface _ params) payable rettype iffs cases posts) =
    -- add parameters to environment
    let env' = addCalldata params env in
    -- check that parameter types are valid
    traverse_ (checkParams env) params *>
    -- check preconditions
    (unzip <$> traverse (checkExpr env' U TBoolean) iffs) `bindValidation` \(iffs', cnstr1) -> do
    let env'' = addPreconds iffs' env'
    -- check cases
    casesc <- unzip <$> traverse (checkBehvCase env'' (argToValueType <$> rettype)) cases
    -- check postconditions
    ensures <- map fst <$> traverse (checkExpr env'' T TBoolean) posts
    -- return the behaviour
    pure $ let (cases', cnstrs2) = casesc
               -- add implicit CALLVALUE == 0 precondition if not payable
               iffs'' = addCallvalueZeroPrecond payable iffs'
               casecnstrs = checkCaseConsistency env' cases'
               -- add integer type bounds as preconditions
               bounds = boundsBehaviour $ Behaviour name contract iface payable iffs'' cases' ensures
               behaviour = Behaviour name contract iface payable (iffs'' <> bounds) cases' ensures
               -- add bound preconditions to constraints
               cnstrs = addIffs bounds $ concat cnstr1 ++ concat cnstrs2 ++ casecnstrs
           in  (behaviour, cnstrs)

-- | Type check a single case of a behaviour
checkBehvCase :: Env -> Maybe ValueType -> U.Case (U.StorageUpdates, Maybe U.Expr)
              -> Err (Bcase Untimed, [Constraint Untimed])
checkBehvCase env rettype (U.Case p cond (updates, mret)) =
    -- check case condition
    checkExpr env U TBoolean cond `bindValidation` \(cond', cnstr1) ->
    -- add case condition to environment preconditions
    let env' = addPreconds [cond'] env in
    -- check storage updates
    (unzip <$> traverse (checkStorageUpdate env') updates) `bindValidation` \(tupdates, cnstr2) -> do
    -- check that storage updates are ordered from least to most specific
    checkOrderedUpdates tupdates
    -- check return expression if any
    res <- case (rettype, mret) of
        (Nothing, Nothing) -> pure Nothing
        (Just (ValueType t), Just e)  ->  Just . first (TExp t) <$> checkExpr env' U t e
        (Nothing, Just _)  -> throw (p, "Behaviour does not return a value, but return expression provided")
        (Just _, Nothing)  -> throw (p, "Behaviour must return a value, but no return expression provided")

    pure $ let (mret', cnstr3) = case res of
                  Just (e, cs) -> (Just e, cs)
                  Nothing -> (Nothing, [])
            in (Case p cond' (tupdates, mret'), cnstr1 ++ concat cnstr2 ++ cnstr3)
    where
        checkOrderedUpdates :: [StorageUpdate] -> Err ()
        checkOrderedUpdates [] = pure ()
        checkOrderedUpdates ((Update _ ref _):upds) =
            (assert (orderErr $ posnFromRef ref) $ not (any (leRef ref . getRef) upds)) *>
            checkOrderedUpdates upds

        orderErr p' = (p', "Storage updates must be listed from the least to most specific")

        getRef :: StorageUpdate -> Ref LHS Untimed
        getRef (Update _ ref _) = ref

        leRef :: Ref LHS Untimed -> Ref LHS Untimed -> Bool
        leRef r1 r2 = r1 == r2 || ltRef r1 r2

        ltRef :: Ref LHS Untimed -> Ref LHS Untimed -> Bool
        ltRef (RField _ r1 _ _) r2 = r1 == r2 || ltRef r1 r2
        ltRef (RArrIdx _ r1 _ _ ) r2 = r1 == r2 || ltRef r1 r2
        ltRef (SVar _ _ _ _) _ = False

-- | Create all combinations of pairs from a list
combine :: [a] -> [(a,a)]
combine lst = combine' lst []
  where
    combine' [] acc = concat acc
    combine' (x:xs) acc =
      let xcomb = [ (x, y) | y <- xs] in
      combine' xs (xcomb:acc)

-- | Create a disjunction (logical OR) of a list of boolean expressions
mkOr :: [Exp ABoolean t] -> Exp ABoolean t
mkOr [] = LitBool nowhere False
mkOr (c:cs) = foldr (Or nowhere) c cs

-- | Create a conjunction (logical AND) of a list of boolean expressions
mkAnd :: [Exp ABoolean t] -> Exp ABoolean t
mkAnd [] = LitBool nowhere True
mkAnd (c:cs) = foldr (And nowhere) c cs


-- | Check if a constructor/transition is non-payable and if so generate a precondition
-- to ensure that it is not called with value.
addCallvalueZeroPrecond :: IsPayable -> [Exp ABoolean Untimed] -> [Exp ABoolean Untimed]
addCallvalueZeroPrecond Payable iffs = iffs
addCallvalueZeroPrecond NonPayable iffs =
    (Eq nowhere (TInteger 256 Unsigned) (IntEnv nowhere Callvalue) (LitInt nowhere 0)) : iffs



-- | Check that case conditions in a case block are mutually exclusive and exhaustive
checkCaseConsistency :: Env -> Cases a -> [Constraint Untimed]
checkCaseConsistency env cases =
    [ BoolCnstr getCasePos "Cases are not mutually exclusive" env (mkNonoverlapAssertion conds)
    , BoolCnstr getCasePos "Cases are not exhaustive" env (mkExhaustiveAssertion conds)
    ]
    where
        getCasePos = case cases of
            [] -> nowhere
            (Case p _ _ : _) -> p

        conds :: [Exp ABoolean Untimed]
        conds = map (\(Case _ cond _) -> cond) cases
        -- For every pair of case conditions we assert that they are true
        -- simultaneously. The query must be unsat.
        mkNonoverlapAssertion :: [Exp ABoolean Untimed] -> Exp ABoolean Untimed
        mkNonoverlapAssertion caseconds =
            mkAnd $ (\(c1, c2) -> Neg nowhere (And nowhere c1 c2)) <$> combine caseconds

        mkExhaustiveAssertion :: [Exp ABoolean Untimed] -> Exp ABoolean Untimed
        mkExhaustiveAssertion caseconds = mkOr caseconds

-- | Type check initial storage assignment
checkAssign :: Env -> U.Assign -> Err (StorageUpdate, [Constraint Untimed])
checkAssign env (U.StorageVar p (ValueType typ) var, expr) = do
    -- check that the type is a valid slot type
    validSlotType env p typ
    -- check the RHS expression
    (expr', cnstr) <- checkExpr env U typ expr
    pure (Update typ (SVar p Neither (contract env) (var)) expr', cnstr)

-- | Check that a type is a valid slot type
validSlotType :: Env -> Pn -> TValueType a -> Err ()
validSlotType _ p (TInteger size _) =
    unless (size `elem` [8,16,32,64,128,256]) $
    throw (p, "Invalid integer size: " <> show size)
validSlotType env p (TContract c) =
    case Map.lookup c (storage env) of
    Just _ -> pure ()
    Nothing -> throw (p, "Contract " <> c <> " is not a valid contract type")
validSlotType _ _  TAddress = pure ()
validSlotType _ _ TBoolean = pure ()
validSlotType _ _ TByteStr = pure ()
validSlotType _ p (TStruct _) = throw (p, "Struct types are not supported yet")
validSlotType _ _ TUnboundedInt = pure ()
validSlotType env p (TArray _ elemtyp) = validSlotType env p elemtyp
validSlotType env p (TMapping (ValueType keytyp) (ValueType val)) =
    assert (p, "Mapping key type must be a base type") (validKeyType keytyp) *>
    assert (p, "Mapping value type cannot be a contract") (validValueType val) *>
    validSlotType env p keytyp *>
    validSlotType env p val
  where
    validKeyType ::  TValueType a -> Bool
    validKeyType TInteger{} = True
    validKeyType TAddress = True
    validKeyType TBoolean = True
    validKeyType TByteStr = True
    validKeyType TUnboundedInt = True
    validKeyType _ = False

    validValueType :: TValueType a -> Bool
    validValueType TContract{} = False
    validValueType TInteger{} = True
    validValueType TAddress = True
    validValueType TBoolean = True
    validValueType TByteStr = True
    validValueType TUnboundedInt = True
    validValueType TArray{} = True
    validValueType TMapping{} = True
    validValueType (TStruct {}) = False


-- | Type check a storage update in a transition case
checkStorageUpdate :: Env -> U.StorageUpdate -> Err (StorageUpdate, [Constraint Untimed])
checkStorageUpdate env (U.Update ref expr) =
    checkRef env SLHS U ref `bindValidation` \(ValueType typ, tref, cnstr) ->
    checkExpr env U typ expr `bindValidation` \(expr', cnstr') ->
    pure (Update typ tref expr', cnstr ++ cnstr')

-- | Type check a variable reference
checkRef :: forall t k. Env -> SRefKind k -> Mode t -> U.Ref -> Err (ValueType, Ref k t, [Constraint t])
-- Single variable reference
checkRef Env{contract, calldata, storage} kind mode (U.RVar p tag name) =
    case Map.lookup name calldata of
      -- calldata variable
      Just typ -> case kind of
        SLHS -> throw (p, "Cannot use calldata variable " <> show name <> " as LHS reference")
        SRHS -> pure (argToValueType typ, CVar p typ name, [])
      Nothing -> case Map.lookup contract storage of
        -- storage variable
        Just storageTyping -> case Map.lookup name storageTyping of
            Just (typ, _) ->
                case (tag, mode) of
                    (U.Neither, U) -> pure (typ, SVar p Neither contract name, [])
                    (U.Pre, T)     -> pure (typ, SVar p Pre contract name, [])
                    (U.Post, T)    -> pure (typ, SVar p Post contract name, [])
                    _              -> throw (p, "Mismatched timing for storage variable " <> show name <> ": declared " <> show tag <> ", used in " <> show mode)
            Nothing -> throw (p, "Unbound variable " <> show name)
        Nothing -> throw (p, "Unbound variable " <> show name) -- accessing storage variable not yet created
-- Indexed reference (mapping or array)
checkRef env kind mode (U.RIndex p en idx) =
  -- check base reference
  checkRef env kind mode en `bindValidation` \(ValueType styp, ref :: Ref k t, cnstr) ->
  case styp of
    TArray len typ@VType ->
        -- check index and add array bound constraint
        checkExpr env mode defaultUInteger idx `bindValidation` \(idx', cnstr') ->
        let arrmsg = "Array index in not guaranteed to be in range for array of length " <> show len in
        pure (ValueType typ, RArrIdx p ref idx' len, makeArrayBoundConstraint p arrmsg env len idx':cnstr ++ cnstr')
    TMapping (ValueType keytyp) (ValueType valtyp) ->
        -- check index
        checkExpr env mode keytyp idx `bindValidation` \(ix, cnstr') ->
        case kind of
            SLHS -> throw (p, "Cannot use mapping indexing as LHS reference")
            SRHS -> pure (ValueType valtyp, RMapIdx p (TRef styp kind ref) (TExp keytyp ix), cnstr ++ cnstr')
    _ -> throw (p, "An indexed reference should have an array or mapping type" <> show en)
-- Storage field access
checkRef env kind mode (U.RField p en x) =
  -- check base reference
  checkRef env kind mode en `bindValidation` \(ValueType styp, ref :: Ref k t, cnstr) ->
  -- look up field type
  case styp of
    TContract c -> case Map.lookup c (storage env) of
      Just cenv -> case Map.lookup x cenv of
        Just (typ, _) ->  pure (typ, RField p ref c x, cnstr)
        Nothing -> throw (p, "Contract " <> c <> " does not have field " <> x)
      Nothing -> error $ "Internal error: Invalid contract type " <> show c
    _ -> throw (p, "Reference should have a contract type" <> show en)

-- | If an `inrange e` predicate appears in the source code, then the inrange
-- predicate is propagated to all subexpressions of `e`.
genInRange :: TValueType AInteger -> Exp AInteger t -> [Exp ABoolean t]
genInRange t e@(LitInt _ _) = [InRange nowhere t e]
genInRange t e@(VarRef _ _ _)  = [InRange nowhere t e]
genInRange t e@(Add _ e1 e2) = [InRange nowhere t e] <> genInRange t e1 <> genInRange t e2
genInRange t e@(Sub _ e1 e2) = [InRange nowhere t e] <> genInRange t e1 <> genInRange t e2
genInRange t e@(Mul _ e1 e2) = [InRange nowhere t e] <> genInRange t e1 <> genInRange t e2
genInRange t e@(Div _ e1 e2) = [InRange nowhere t e] <> genInRange t e1 <> genInRange t e2
genInRange t e@(Mod _ e1 e2) = [InRange nowhere t e] <> genInRange t e1 <> genInRange t e2
genInRange t e@(Exp _ e1 e2) = [InRange nowhere t e] <> genInRange t e1 <> genInRange t e2
genInRange t e@(IntEnv _ _) = [InRange nowhere t e]
genInRange t e@(Address _ _ _) = [InRange nowhere t e]
genInRange _ (IntMin _ _)  = error "Internal error: invalid range expression"
genInRange _ (IntMax _ _)  = error "Internal error: invalid range expression"
genInRange _ (UIntMin _ _) = error "Internal error: invalid range expression"
genInRange _ (UIntMax _ _) = error "Internal error: invalid range expression"
genInRange _ (ITE _ _ _ _) = error "Internal error: invalid range expression"


typeMismatchErr :: forall a b res. Pn -> TValueType a -> TValueType b -> Err res
typeMismatchErr p t1 t2 = throw (p, "Type " <> prettyTValueType t1 <> " should match type " <> prettyTValueType t2)

relaxedValueEquality :: ValueType -> ValueType -> Bool
relaxedValueEquality (ValueType t1) (ValueType t2) = isJust $ relaxedtestEquality t1 t2

-- | Relaxed equality for types that considers all integer types as equal
relaxedtestEquality :: TValueType a -> TValueType b -> Maybe (a :~: b)
relaxedtestEquality (TInteger _ _) (TInteger _ _) = Just Refl
relaxedtestEquality (TInteger _ _) TUnboundedInt = Just Refl
relaxedtestEquality TUnboundedInt (TInteger _ _) = Just Refl
relaxedtestEquality TUnboundedInt TUnboundedInt = Just Refl
relaxedtestEquality (TArray n1 t1) (TArray n2 t2) | n1 == n2 = relaxedtestEquality t1 t2 >>= \Refl -> Just Refl
relaxedtestEquality (TMapping k1 t1) (TMapping k2 t2) =
  if relaxedValueEquality k1 k2 && relaxedValueEquality t1 t2 then Just Refl else Nothing
relaxedtestEquality (TStruct fs1) (TStruct fs2) =
  if all (uncurry relaxedValueEquality) (zip fs1 fs2) then Just Refl else Nothing
relaxedtestEquality t1 t2 = testEquality t1 t2

relaxedIntCheck :: TValueType a -> TValueType b -> Bool
relaxedIntCheck t1 t2 = isJust $ relaxedtestEquality t1 t2

-- | Check that two types are equal under the relaxed equality
checkEqType :: forall a b. Pn -> TValueType a -> TValueType b -> Err ()
checkEqType p t1 t2 =
    if relaxedIntCheck t1 t2 then pure ()
    else typeMismatchErr p t1 t2

-- | Combines two types that should satisfy the relaxedtestEquality to the most general type
combineTypes :: TValueType a -> TValueType a -> TValueType a
combineTypes (TInteger w1 Signed) (TInteger w2 Signed) = TInteger (max w1 w2) Signed
combineTypes (TInteger w1 Unsigned) (TInteger w2 Unsigned) = TInteger (max w1 w2) Unsigned
combineTypes (TInteger w1 Signed) (TInteger w2 Unsigned) =
    if w1 > w2 then TInteger w1 Signed
    else TUnboundedInt
combineTypes (TInteger w1 Unsigned) (TInteger w2 Signed) =
    if w2 > w1 then TInteger w2 Signed
    else TUnboundedInt
combineTypes TUnboundedInt TUnboundedInt = TUnboundedInt
combineTypes (TInteger _ _) TUnboundedInt = TUnboundedInt
combineTypes TUnboundedInt (TInteger _ _) = TUnboundedInt
combineTypes (TArray n1 t1') (TArray _ t2') =
    let c = combineTypes t1' t2'
    in TArray n1 c
combineTypes t1 _ = t1

fitsIn :: TValueType AInteger -> TValueType AInteger -> Bool
fitsIn (TInteger w1 s1) (TInteger w2 s2)
  | s1 == s2 = w1 <= w2
  | s1 == Unsigned && s2 == Signed = w1 < w2
  | otherwise = False
fitsIn TUnboundedInt (TInteger _ _) = False
fitsIn (TInteger _ _) TUnboundedInt = True
fitsIn TUnboundedInt TUnboundedInt = True
fitsIn TAddress _ = False -- for now do not coerce address to integer
fitsIn _ TAddress = False

-- | Check if the given expression can be typed with the given type
checkExpr :: forall t a. Env -> Mode t -> TValueType a -> U.Expr -> Err (Exp a t, [Constraint t])
-- Mapping Expressions
checkExpr env mode mtyp@(TMapping (ValueType keytyp) (ValueType valtyp)) (U.MappingUpd p ref mapexp) = do
    checkRef env SRHS mode ref `bindValidation` \(ValueType rtyp, tref, cnstr1) -> do
        checkEqType p mtyp rtyp
        updsc <- unzip <$> traverse (\(k,v) -> do
            kc <- checkExpr env mode keytyp k
            vc <- checkExpr env mode valtyp v
            pure $ let (k', cnstr2) = kc
                       (v', cnstr3) = vc
                   in ((k', v'), cnstr2 ++ cnstr3)) mapexp
        pure $ let (updates, cnstr2) = updsc in
           (MappingUpd p tref keytyp valtyp updates, cnstr1 ++ concat cnstr2)
checkExpr env mode (TMapping (ValueType keytyp) (ValueType valtyp)) (U.Mapping p mapexp) = do
    mapc <- unzip <$> traverse (\(k,v) -> do
        kc <- checkExpr env mode keytyp k
        vc <- checkExpr env mode valtyp v
        pure $ let (k', cnstr2) = kc
                   (v', cnstr3) = vc
                in ((k', v'), cnstr2 ++ cnstr3)) mapexp
    pure $ let (map', cnstr1) = mapc in
           (Mapping p keytyp valtyp map', concat cnstr1)
-- Integer Expressions
checkExpr env mode t1@(TInteger _ _) e =
    inferExpr env mode e `bindValidation` \(TExp t2 te, cs) -> do
    let msg = "Integer expression of type " <> prettyTValueType t2 <> " is not guaranteed to fit in type " <> prettyTValueType t1
    case t2 of
        (TInteger _ _) ->
            if t2 `fitsIn` t1 then pure (te, cs)
            else pure (te, cs ++ [makeIntegerBoundConstraint (getPosn e) msg env t1 te])
        TUnboundedInt -> pure (te, cs ++ [makeIntegerBoundConstraint (getPosn e) msg env t1 te])
        _ -> typeMismatchErr (getPosn e) t1 t2
checkExpr env mode t1@TUnboundedInt e =
    inferExpr env mode e `bindValidation` \(TExp t2 te, cs) -> do
    case t2 of
        (TInteger _ _) -> pure (te, cs)
        TUnboundedInt -> pure (te, cs)
        _ -> typeMismatchErr (getPosn e) t1 t2
-- Array Expressions
-- TODO: all array cases except the last are probably not necessary, but may lead to nicer error messages,
-- less unnecessary constraints and prettier code.
-- The idea is that we can avoid unnecessary constraint enforcement by using `checkExpr` on each element
-- If, instead, the whole array is inferred first, we are then forced to apply
checkExpr env mode (TArray len t) (U.EArray p es) = do
    if len == length es then pure () else typeMismatchErr p (TArray len t) (TArray (length es) t)
    r <- unzip <$> traverse (checkExpr env mode t) es
    pure $ let (tes,cs) = r in (Array p tes, concat cs)
checkExpr _ _ t (U.EArray p _) = throw (p, "Array expression cannot have type " <> prettyTValueType t)
checkExpr env mode t@(TArray _ _) (U.EITE p e1 e2 e3) = do
    r1 <- checkExpr env mode TBoolean e1
    r2 <- checkExpr env mode t e2
    r3 <- checkExpr env mode t e3
    pure $ let (te1, cnstr1) = r1
               (te2, cnstr2) = r2
               (te3, cnstr3) = r3
           in (ITE p te1 te2 te3, cnstr1 ++ cnstr2 ++ cnstr3)
checkExpr env mode t1@(TArray _ _) e =
    -- Question: do we allow array subtyping here?
    let pn = getPosn e in
    inferExpr env mode e `bindValidation` \(TExp t2 te, cs) ->
        flip (maybe (typeMismatchErr pn t1 t2)) (relaxedtestEquality t1 t2) $ \Refl ->
            case (fst $ flattenValueType t1, fst $ flattenValueType t2) of
                (bt1@(TInteger _ _), bt2@(TInteger _ _)) ->
                    let msg = "Array element integer expression of type " <> prettyTValueType bt2 <> " is not guaranteed to fit in type " <> prettyTValueType bt1 in
                    if bt2 `fitsIn` bt1 then pure (te, cs)
                    else pure (te, cs ++ (makeIntegerBoundConstraint (getPosn e) msg env bt1 <$> expandArrayExpr t2 te))
                (bt1@(TInteger _ _), TUnboundedInt) ->
                    let msg = "Array element integer expression of type " <> prettyTValueType TUnboundedInt <> " is not guaranteed to fit in type " <> prettyTValueType bt1 in
                    pure (te, cs ++ (makeIntegerBoundConstraint (getPosn e) msg env bt1 <$> expandArrayExpr t2 te))
                (TUnboundedInt, TInteger _ _) -> pure (te, cs)
                (TUnboundedInt, TUnboundedInt) -> pure (te, cs)
                _ -> typeMismatchErr (getPosn e) t1 t2
checkExpr env mode t1 e =
    let pn = getPosn e in
    inferExpr env mode e `bindValidation` \(TExp t2 te, cs) ->
    maybe (typeMismatchErr pn t1 t2) (\Refl -> pure (te, cs)) $ testEquality t1 t2


-- | Attempt to infer a type of an expression. If successful, it returns an
-- existential package of the infered typed together with the typed expression.
inferExpr :: forall t. Env -> Mode t -> U.Expr -> Err (TypedExp t, [Constraint t])
inferExpr env@Env{constructors} mode e = case e of
  -- Boolean expressions
  U.ENot    p v1    -> first (wrapOp (Neg  p) TBoolean) <$> checkExpr env mode TBoolean v1
  U.EAnd    p v1 v2 -> boolOp2 (And  p) TBoolean v1 v2
  U.EOr     p v1 v2 -> boolOp2 (Or   p) TBoolean v1 v2
  U.EImpl   p v1 v2 -> boolOp2 (Impl p) TBoolean v1 v2
  U.ELT     p v1 v2 -> boolOp2 (LT   p) TUnboundedInt v1 v2
  U.ELEQ    p v1 v2 -> boolOp2 (LEQ  p) TUnboundedInt v1 v2
  U.EGEQ    p v1 v2 -> boolOp2 (GEQ  p) TUnboundedInt v1 v2
  U.EGT     p v1 v2 -> boolOp2 (GT   p) TUnboundedInt v1 v2
  U.EEq     p v1 v2 -> first (TExp TBoolean) <$> polycheck p Eq v1 v2
  U.ENeq    p v1 v2 -> first (TExp TBoolean) <$> polycheck p NEq v1 v2
  U.BoolLit p v1    -> pure (TExp TBoolean (LitBool p v1), [])
  U.EInRange _ (fromAbiType -> ValueType tr@(TInteger _ _)) v ->
    inferExpr env mode v `bindValidation` \(TExp t te, cnstr) ->
    case t of
      TInteger _ _ -> pure (TExp TBoolean . andExps $ genInRange tr te, cnstr)
      TUnboundedInt -> pure (TExp TBoolean . andExps $ genInRange tr te, cnstr)
      _ -> throw (getPosn e, "inRange can only be applied to integer expressions")
  U.EInRange _ _ _ -> throw (getPosn e, "inRange can be used only with integer types")
  U.EAdd   p v1 v2 -> arithOp2 (Add p) v1 v2
  U.ESub   p v1 v2 -> arithOp2 (Sub p) v1 v2
  U.EMul   p v1 v2 -> arithOp2 (Mul p) v1 v2
  U.EDiv   p v1 v2 -> arithOp2 (Div p) v1 v2
  U.EMod   p v1 v2 -> arithOp2 (Mod p) v1 v2
  U.EExp   p v1 v2 -> arithOp2 (Exp p) v1 v2
  U.IntLit p v1    ->
    pure (TExp (litBoundedType v1) (LitInt p v1), [])
   where
    -- Determine the narrowest integer type that can hold the given literal value
    litBoundedType :: Integer -> TValueType AInteger
    litBoundedType v | v >= 0 && v <= maxUnsigned 256 = TInteger (findBoundUnsigned v) Unsigned
                      | otherwise && v >= minSigned 256 && v <= maxSigned 256 = TInteger (findBoundSigned v) Signed
                      | otherwise = TUnboundedInt

  U.EArray p l -> (unzip <$> traverse (inferExpr env mode) l) `bindValidation` \(tes, cs) ->
    (, concat cs) <$> gatherElements tes
    where
      gatherElements :: [TypedExp t] -> Err (TypedExp t)
      gatherElements (TExp t1 te1:tes) =  TExp (TArray (length l) t1) <$> (Array p . (:) te1 <$> traverse (checkElement t1) tes)
      gatherElements [] = throw (p, "Internal error: Cannot infer type of empty array expression")

      -- TODO: this relies on combineTypes, look that over as it is not complete
      -- combinedType :: [TValueType a] -> Err (TValueType a)
      -- combinedType ts@(th : tl) = foldl' (\ta tb -> ta `bindValidation` combineTypes tb) (pure th) ts

      checkElement :: TValueType a -> TypedExp t -> Err (Exp a t)
      checkElement t (TExp t' te) = maybe (typeMismatchErr (posnFromExp te) t t') (\Refl -> pure te) $ relaxedtestEquality t t'

  -- Constructor calls
  U.ECreate p c args callvalue -> case Map.lookup c constructors of
    Just cnstr -> do
        let sig = map (\(Arg typ _) -> typ) (case _cinterface cnstr of Interface _ as -> as)
            payable = _cisPayable cnstr
        cvc <- case (payable, callvalue) of
                (NonPayable, Just _) -> throw (p, "Constructor " <> show c <> " is not payable, but call value provided")
                (Payable, Just cvExpr) -> first Just <$> checkExpr env mode (TInteger 256 Unsigned) cvExpr
                (NonPayable, Nothing)    -> pure (Nothing, [])
                (Payable, Nothing)     -> pure (Just $ LitInt nowhere 0, [])
        argsc <- checkArgs env mode p (argToValueType <$> sig) args
        pure $ let (args', cnstr1) = argsc
                   (cv, cnstr2) = cvc
                   callcnstr = CallCnstr p msg env args' c
                   msg = "Preconditions of constructor call to " <> show c <> " are not guaranteed to hold"
                in (TExp (TContract c) (Create p c args' cv), callcnstr:cnstr1 ++ cnstr2)
    Nothing -> throw (p, "Unknown constructor " <> show c)
  -- Control
  U.EITE p e1 e2 e3 ->
    ((,,) <$> (checkExpr env mode TBoolean e1) <*> (inferExpr env mode e2) <*> (inferExpr env mode e3))
    `bindValidation` \((te1, cnstr1), (TExp t2 te2, cnstr2), (TExp t3 te3, cnstr3)) ->
      case relaxedtestEquality t2 t3 of
        Nothing   -> typeMismatchErr p t2 t3
        Just Refl -> pure (TExp (combineTypes t2 t3) (ITE p te1 te2 te3), cnstr1 ++ cnstr2 ++ cnstr3)
  -- Environment variables
  U.EnvExp p v -> pure (TExp (ethEnv v) (IntEnv p v), [])
  -- Variable references
  U.ERef ref ->
    (\(ValueType typ, tref, cnstr) -> (TExp typ (VarRef (getPosRef ref) typ tref), cnstr)) <$> checkRef env SRHS mode ref
  -- Address-of operator
  U.AddrOf p e1 -> do
    inferExpr env mode e1 `bindValidation` \(TExp ty e', cnstr) ->
      case ty of
        TContract c -> pure (TExp TAddress (Address p c e'), cnstr)
        _ -> throw (p, "Expression of type " <> show ty <> " cannot be converted to address")
  -- Mapping Epxressions
  U.Mapping p _ -> throw (p, "The type of mappings cannot be inferred.")
  U.MappingUpd p _ _ -> throw (p, "The type of mappings cannot be inferred.")
  _ -> undefined
  where
    wrapOp f t e1 = TExp t (f e1) -- use sign to let Haskell automatically derive the type here
    --wrapOp2 f t e1 e2 = TExp t (f e1 e2)

    boolOp2 :: forall a. (Exp a t -> Exp a t -> Exp ABoolean t) -> TValueType a -> U.Expr -> U.Expr -> Err (TypedExp t, [Constraint t])
    boolOp2 f t e1 e2 = do
      (\(e1', c1) (e2', c2) -> (TExp TBoolean (f e1' e2'), c1 ++ c2)) <$> checkExpr env mode t e1 <*> checkExpr env mode t e2
    arithOp2 :: (Exp AInteger t -> Exp AInteger t -> Exp AInteger t) -> U.Expr -> U.Expr -> Err (TypedExp t, [Constraint t])
    arithOp2 f e1 e2 = do
      -- Could generate more precise int type here
      (\(e1', c1) (e2', c2) -> (TExp TUnboundedInt (f e1' e2'), c1 ++ c2)) <$> checkExpr env mode TUnboundedInt e1 <*> checkExpr env mode TUnboundedInt e2
    polycheck :: forall z. Pn -> (forall y. Pn -> TValueType y -> Exp y t -> Exp y t -> z) -> U.Expr -> U.Expr -> Err (z, [Constraint t])
    polycheck pn cons e1 e2 = do
       ((,) <$> (inferExpr env mode e1) <*> (inferExpr env mode e2)) `bindValidation` \( (TExp t1 te1, c1), (TExp t2 te2, c2) ) ->
        case relaxedtestEquality t1 t2 of
          Nothing   -> typeMismatchErr pn t1 t2
          Just Refl -> pure (cons pn t1 te1 te2, c1 ++ c2)


-- | Type check a list of argument expressions against a list of expected types
checkArgs :: forall t. Env -> Mode t -> Pn -> [ValueType] -> [U.Expr] -> Err ([TypedExp t], [Constraint t])
checkArgs _ _ _ [] [] = pure ([], [])
checkArgs env mode pn (ValueType t:types) (e:exprs) =
    (\(e', cnstr1) (es', cnstr2) -> (TExp t e' : es', cnstr1 ++ cnstr2)) <$> checkExpr env mode t e <*> checkArgs env mode pn types exprs

checkArgs _ _ pn _ _ = throw (pn, "Argument length mismatch")

-- | Compute the maximum unsigned integer value for a given bit size
maxUnsigned :: Int -> Integer
maxUnsigned bits = 2 ^ bits - 1

-- | Compute the maximum signed integer values for a given bit size
maxSigned :: Int -> Integer
maxSigned bits = 2 ^ (bits - 1) - 1

-- | Compute the minimum signed integer value for a given bit size
minSigned :: Int -> Integer
minSigned bits = - (2 ^ (bits - 1))

-- | Find the smallest bit size that can hold the given signed integer value
findBoundSigned :: Integer -> Int
findBoundSigned v = go 8
  where
    go bits | v >= minSigned bits && v <= maxSigned bits = bits
            | bits >= 256 = 256
            | otherwise   = go (bits + 8)

-- | Find the smallest bit size that can hold the given unsigned integer value
findBoundUnsigned :: Integer -> Int
findBoundUnsigned v = go 8
  where
    go bits | 0 <= v && v <= maxUnsigned bits = bits
            | bits >= 256 = 256
            | otherwise   = go (bits + 8)

-- | Check if an integer expression can be represented as a 256-bit signed or unsigned integer
-- This is usefull for deciding whether to use signed or unsigned operations in hevm symbolic execution
-- Assumes that no overflows or underflows can occur in the expression
hasSign ::  IntSign -> Exp AInteger t -> Bool
hasSign s (LitInt _ n) = hasSignLit s n
hasSign s (Add _ e1 e2) = hasSign s e1 && hasSign s e2
hasSign s (Sub _ e1 e2) = hasSign s e1 && hasSign s e2
hasSign s (Mul _ e1 e2) = hasSign s e1 && hasSign s e2
hasSign s (Div _ e1 e2) = hasSign s e1 && hasSign s e2
hasSign s (Mod _ e1 e2) = hasSign s e1 && hasSign s e2
hasSign s (Exp _ e1 e2) = hasSign s e1 && hasSign s e2
hasSign _ (IntEnv _ _) = True
hasSign _ (Address _ _ _) = True
hasSign s (ITE _ _ e2 e3) = hasSign s e2 && hasSign s e3 -- ITE always results in signed integers
hasSign Signed (IntMin _ _) = True
hasSign Unsigned (IntMin _ _) = False
hasSign Signed (IntMax _ _) = True
hasSign Unsigned (IntMax _ _) = False
hasSign _ (UIntMin _ _) = True
hasSign _ (UIntMax _ _) = True
hasSign s (VarRef _ (TInteger _ s') _) = s == s'
hasSign _ (VarRef _ TUnboundedInt _) = False
hasSign _ (VarRef _ TAddress _) = True

-- | Check if a literal integer value can be represented as a 256-bit signed or unsigned integer
hasSignLit :: IntSign -> Integer -> Bool
hasSignLit Signed v = minSigned 256 <= v && v <= maxSigned 256
hasSignLit Unsigned v = 0 <= v && v <= maxUnsigned 256