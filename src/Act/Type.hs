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

module Act.Type (typecheck, Err) where

import Prelude hiding (GT, LT)

import EVM.ABI
import Data.Map.Strict    (Map)
import Data.Bifunctor (first, second, bimap)
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty (toList)
import qualified Data.Map.Strict    as Map
import Data.Typeable ( Typeable, (:~:)(Refl), eqT )
import Type.Reflection (typeRep)

import Control.Monad (when, unless)
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
import Control.Monad.Accum (MonadAccum(add))
import Control.Lens (Cons, Const (Const))
import Act.Syntax.Untyped (Expr(BoolLit))


type Err = Error String

-- | A map containing the interfaces of all available constructors, a payable flag, and the constructor preconditions.
type Constructors = Map Id ([ArgType], IsPayable, [Exp ABoolean Untimed])

-- | The type checking environment.
data Env = Env
  { contract     :: Id                           -- ^ The name of the current contract.
  , storage      :: StorageTyping                -- ^ StorageTyping
  , calldata     :: Map Id ArgType               -- ^ The calldata var names and their types.
  , constructors :: Constructors                 -- ^ Interfaces and preconditions of constructors
  }
  deriving (Show)

emptyEnv :: Env
emptyEnv = Env
  { contract     = ""
  , storage      = mempty
  , calldata     = mempty
  , constructors = mempty
  }


-- | Functions to manipulate environments
addCalldata :: [Arg] -> Env -> Env
addCalldata decls env = env{ calldata = abiVars }
  where
   abiVars = Map.fromList $ map (\(Arg typ var) -> (var, typ)) decls

addConstrStorage :: Id -> Map Id (ValueType, Integer) -> Env -> Env
addConstrStorage id storageTyping env = env { storage = Map.insert id storageTyping (storage env) }

addConstructor :: Id -> [ArgType] -> IsPayable -> [Exp ABoolean Untimed] -> Env -> Env
addConstructor cid args payable iffs env =
  env { constructors = Map.insert cid (args, payable, iffs) (constructors env) }

-- | Constraints generated during type checking.
-- An integer constraint constrains an integer expression to fit within the bounds of a given type.
-- A call constraint constrains the arguments of a constructor call to satisfy the constructor's preconditions.
data Constraint t =
    BoolCnstr Pn (Exp ABoolean t)
  | CallCnstr Pn [TypedExp t] Id
    deriving (Show, Eq)

makeIntegerBoundConstraint :: Pn -> TValueType AInteger -> Exp AInteger t -> Constraint t
makeIntegerBoundConstraint p t e = BoolCnstr p (InRange nowhere t e)

makeArrayBoundConstraint :: Pn -> Int -> Exp AInteger t -> Constraint t
makeArrayBoundConstraint p len e = BoolCnstr p (LT p e (LitInt p (fromIntegral len)))

-- | Top-level typechecking function
typecheck :: U.Act -> Err Act
typecheck (U.Main contracts) = do
    uncurry Act <$> checkContracts' contracts
    
checkContracts' :: [U.Contract] -> Err (StorageTyping, [Contract])
checkContracts' cs = first storage <$> checkContracts emptyEnv cs

checkContracts :: Env -> [U.Contract] -> Err (Env, [Contract])
checkContracts env [] = pure (env, [])
checkContracts env ((U.Contract cnstr behvs):cs) =
    checkConstructor env cnstr `bindValidation` \(constr', env') -> do
    behvs' <- checkBehaviours env' behvs
    (env'', cs') <- checkContracts env' cs
    pure (env'', Contract constr' behvs' : cs')
    

checkConstructor :: Env -> U.Constructor -> Err (Constructor, Env)
checkConstructor env (U.Constructor posn cid (Interface _ params) payable iffs cases posts invs) =
    -- check that parameter types are valid
    traverse_ (checkParams env) params *>
    -- check that the constructor name is not already defined
    checkConstrName cid env *>
    -- check preconditions
    (unzip <$> traverse (checkExpr env' U TBoolean) iffs) `bindValidation` \(iffs', cnstr1) ->
    -- check postconditions
    (checkConstrCases env' cases) `bindValidation` \(storageType, cases', cnstr2) -> do
    -- construct the new environment
    let env'' = addConstrStorage cid storageType $ addConstructor cid argTypes payable iffs' env'
    -- check postconditions
    ensures <- fst . unzip <$> traverse (checkExpr env'' U TBoolean) posts
    -- return the constructor and the new environment
    pure (Constructor cid (Interface cid params) payable iffs' cases' ensures [], env'')         
    where
        env' = addCalldata params env

        checkConstrName :: Id -> Env -> Err ()
        checkConstrName cid Env{constructors} =
            case Map.lookup cid constructors of
                Just _ -> throw (posn, "Constructor " <> cid <> " is already defined")
                Nothing -> pure ()
        
        argTypes :: [ArgType]
        argTypes = map (\(Arg typ _) -> typ) params

checkParams :: Env -> U.Arg -> Err ()
checkParams Env{storage} (Arg (ContractArg p c) _) =
  case Map.lookup c storage of
    Nothing -> throw (p, "Contract " <> c <> " is not a valid contract type")
    Just _ -> pure ()
-- TODO check that abi types are valid
checkParams _ _ = pure ()

checkConstrCases :: Env -> [U.Case U.Creates]
                 -> Err (Map Id (ValueType, Integer), Cases [StorageUpdate], [(Exp ABoolean Untimed, [Constraint Untimed])])
checkConstrCases env cases = do
  checkCases cases `bindValidation` \(cases', cnstr) -> do
    storageTyping <- checkStorageTyping cases
    pure (storageTyping, cases', cnstr)
  where
    checkCases :: [U.Case U.Creates] -> Err (Cases [StorageUpdate], [(Exp ABoolean Untimed, [Constraint Untimed])])
    checkCases [] = pure ([], [])
    checkCases ((U.Case _ cond assigns):cases) = do
        r1 <- checkExpr env U TBoolean cond
        r2 <- unzip <$> traverse (checkAssign env) assigns
        r3 <- checkCases cases
        -- because we use applicative-do we need to do all of the bindings inside pure
        pure $ let (cases', cnstr3) = r3 in
               let (c, cnstr1) = r1 in
               let (updates, cnstr2) = r2 in
               ((c, updates):cases', (LitBool nowhere True, cnstr1):(c, concat cnstr2):cnstr3)
        
    checkStorageTyping :: [U.Case U.Creates] -> Err (Map Id (ValueType, Integer))
    checkStorageTyping [] = pure mempty
    checkStorageTyping ((U.Case _ _ assigns):_) = do
        let typing = makeStorageTyping assigns 0
        consistentStorageTyping typing cases
        pure $ Map.fromList typing

    -- make the storage typing from a list of assignments
    makeStorageTyping :: [U.Assign] -> Integer ->  [(Id, (ValueType, Integer))]
    makeStorageTyping [] _ = []
    makeStorageTyping ((U.StorageVar _ typ name, _):rest) slot = (name, (typ, slot)):makeStorageTyping rest (slot + 1)

    -- check that the storage typing is the same across all cases
    consistentStorageTyping :: [(Id, (ValueType, Integer))] -> [U.Case U.Creates] -> Err ()
    consistentStorageTyping _ [] = pure ()
    consistentStorageTyping typing ((U.Case p _ assigns):cases) =
        let typing' = makeStorageTyping assigns 0 in
        consistentStorageTyping typing cases *>
        assert (p, "Inconsistent storage typing in constructor cases") (typing == typing')

checkBehaviours :: Env -> [U.Transition] -> Err [Behaviour]
checkBehaviours _ [] = pure []
checkBehaviours env (b:bs) = do
    checkBehvName b bs
    b' <- checkBehaviour env b
    bs' <- checkBehaviours env bs
    pure $ b':bs'

    where
        checkBehvName :: U.Transition -> [U.Transition] -> Err ()
        checkBehvName (U.Transition pn name _ _ _ _ _ _) bs =
            case find (\(U.Transition _ n _ _ _ _ _ _) -> n == name) bs of
                Just _ -> throw (pn, "Behaviour " <> name <> "for contract " <> contract env <> " is already defined")
                Nothing -> pure ()


checkBehaviour :: Env -> U.Transition -> Err Behaviour
checkBehaviour env@Env{contract} (U.Transition posn name _ iface@(Interface _ params) payable iffs cases posts) = do
    traverse_ (checkParams env) params
    let env' = addCalldata params env
    iffs' <- fst . unzip <$> traverse (checkExpr env U TBoolean) iffs
    -- TODO check case consistency
    cases' <- fst . unzip <$> traverse (checkBehvCase env') cases
    ensures <- fst . unzip <$> traverse (checkExpr env' T TBoolean) posts
    pure $ Behaviour name contract iface payable iffs' cases' ensures


checkBehvCase :: Env -> U.Case (U.StorageUpdates, Maybe U.Expr)
              -> Err ((Exp ABoolean Untimed, ([StorageUpdate], Maybe (TypedExp Untimed))), [(Exp ABoolean Untimed, [Constraint Untimed])])
checkBehvCase env (U.Case _ cond (updates, mret)) = do
    contcnstr <- checkExpr env U TBoolean cond
    updcnstr <- unzip <$> traverse (checkStorageUpdate env) updates
    res <- traverse (inferExpr env U) mret
    pure $ let (cond', cnstr1) = contcnstr
               (storageUpdates, cnstr2) = updcnstr
               (mret', cnstr3) = case res of
                  Just (e, cs) -> (Just e, cs)
                  Nothing -> (Nothing, [])
            in ((cond', (storageUpdates, mret')), [(LitBool nowhere True, cnstr1), (cond', concat cnstr2 ++ cnstr3)])

checkAssign :: Env -> U.Assign -> Err (StorageUpdate, [Constraint Untimed])
checkAssign env (U.StorageVar p (ValueType typ) var, expr) = do
    validSlotType env p typ
    (expr', cnstr) <- checkExpr env U typ expr
    pure (Update typ (SVar p Neither (contract env) (var)) expr', cnstr)
  where
    validSlotType :: Env -> Pn -> TValueType a -> Err ()
    validSlotType _ p (TInteger size _) =
      unless (size `elem` [8,16,32,64,128,256]) $
        throw (p, "Invalid integer size: " <> show size)
    validSlotType env p (TContract c) =
      case Map.lookup c (storage env) of
        Just _ -> pure ()
        Nothing -> throw (p, "Contract " <> c <> " is not a valid contract type")
    validSlotType _ _ _ = pure ()

checkStorageUpdate :: Env -> U.StorageUpdate -> Err (StorageUpdate, [Constraint Untimed])
checkStorageUpdate env (U.Update ref expr) =
    checkRef env SLHS U ref `bindValidation` \(ValueType typ, tref, cnstr) ->
    checkExpr env U typ expr `bindValidation` \(expr', cnstr') ->
    pure (Update typ tref expr', cnstr ++ cnstr')

checkRef :: forall t k. Env -> SRefKind k -> Mode t -> U.Ref -> Err (ValueType, Ref k t, [Constraint t])
checkRef Env{contract, calldata, storage} kind mode (U.RVar p tag name) =
    case Map.lookup name calldata of
      Just typ -> case kind of
        SLHS -> throw (p, "Cannot use calldata variable " <> show name <> " as LHS reference")
        SRHS -> pure (argToValueType typ, CVar p typ name, [])
      Nothing -> case Map.lookup contract storage of
        Just storageTyping -> case Map.lookup name storageTyping of
            Just (typ, _) ->
                case (tag, mode) of
                    (U.Neither, U) -> pure (typ, SVar p Neither contract name, [])
                    (U.Pre, T)     -> pure (typ, SVar p Pre contract name, [])
                    (U.Post, T)    -> pure (typ, SVar p Post contract name, [])
                    _              -> throw (p, "Mismatched timing for storage variable " <> show name <> ": declared " <> show tag <> ", used in " <> show mode)
            Nothing -> throw (p, "Unbound variable " <> show name)
        Nothing -> throw (nowhere, "Contract " <> contract <> " undefined") -- unreachable
checkRef env kind mode (U.RIndex p en idx) =
  checkRef env kind mode en `bindValidation` \(ValueType styp, ref :: Ref k t, cnstr) ->
  case styp of
    TArray len typ@VType ->
        checkExpr env mode defaultUInteger idx `bindValidation` \(idx', cnstr') ->
        pure (ValueType typ, RArrIdx p ref idx' len, makeArrayBoundConstraint p len idx':cnstr ++ cnstr')
    mtyp@(TMapping (ValueType keytyp) (ValueType valtyp)) ->
        checkExpr env mode keytyp idx `bindValidation` \(ix, cnstr') ->
        case kind of
            SLHS -> throw (p, "Cannot use mapping indexing as LHS reference")
            SRHS -> pure (ValueType valtyp, RMapIdx p (TRef mtyp kind ref) (TExp keytyp ix), cnstr ++ cnstr')
    _ -> throw (p, "An indexed reference should have an array or mapping type" <> show en)
checkRef env kind mode (U.RField p en x) =
  checkRef env kind mode en `bindValidation` \(ValueType styp, ref :: Ref k t, cnstr) ->
  case styp of
    TContract c -> case Map.lookup c (storage env) of
      Just cenv -> case Map.lookup x cenv of
        Just (typ, _) ->  pure (typ, RField p ref c x, cnstr)
        Nothing -> throw (p, "Contract " <> c <> " does not have field " <> x)
      Nothing -> error $ "Internal error: Invalid contract type " <> show c
    _ -> throw (p, "Reference should have a contract type" <> show en)
checkRef _ _ _ _ = error "Internal error: invalid reference"

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
genInRange t e@(Address _ _) = [InRange nowhere t e]
genInRange _ (IntMin _ _)  = error "Internal error: invalid range expression"
genInRange _ (IntMax _ _)  = error "Internal error: invalid range expression"
genInRange _ (UIntMin _ _) = error "Internal error: invalid range expression"
genInRange _ (UIntMax _ _) = error "Internal error: invalid range expression"
genInRange _ (ITE _ _ _ _) = error "Internal error: invalid range expression"


typeMismatchErr :: forall a b res. Pn -> TValueType a -> TValueType b -> Err res
typeMismatchErr p t1 t2 = (throw (p, "Type " <> show t1 <> " should match type " <> show t2))

arrayTypeMismatchErr :: forall a b res. Pn -> TValueType a -> TValueType b -> Err res
arrayTypeMismatchErr p t1 t2 = (throw (p, "Inconsistent array type: Type " <> show t1 <> " should match type " <> show t2))

relaxedtestEquality :: TValueType a -> TValueType b -> Maybe (a :~: b)
relaxedtestEquality (TInteger _ _) (TInteger _ _) = Just Refl
relaxedtestEquality (TInteger _ _) TUnboundedInt = Just Refl
relaxedtestEquality TUnboundedInt (TInteger _ _) = Just Refl
relaxedtestEquality TUnboundedInt TUnboundedInt = Just Refl
relaxedtestEquality t1 t2 = testEquality t1 t2

relaxedIntCheck :: TValueType a -> TValueType b -> Bool
relaxedIntCheck t1 t2 = isJust $ relaxedtestEquality t1 t2

checkEqType :: forall a b. Pn -> TValueType a -> TValueType b -> Err ()
checkEqType p t1 t2 =
    if relaxedIntCheck t1 t2 then pure ()
    else typeMismatchErr p t1 t2

-- | Combines two types that should satisfy the relaxedtestEquality to the most general type
combineTypes :: TValueType a -> TValueType a -> Err (TValueType a)
combineTypes (TInteger w1 Signed) (TInteger w2 Signed) = pure $ TInteger (max w1 w2) Signed
combineTypes (TInteger w1 Unsigned) (TInteger w2 Unsigned) = pure $ TInteger (max w1 w2) Unsigned
combineTypes (TInteger w1 Signed) (TInteger w2 Unsigned) =
    if w1 > w2 then pure (TInteger w1 Signed)
    else pure TUnboundedInt
combineTypes (TInteger w1 Unsigned) (TInteger w2 Signed) =
    if w2 > w1 then pure (TInteger w2 Signed)
    else pure TUnboundedInt
combineTypes TUnboundedInt TUnboundedInt = pure TUnboundedInt
combineTypes (TInteger _ _) TUnboundedInt = pure TUnboundedInt
combineTypes TUnboundedInt (TInteger _ _) = pure TUnboundedInt
combineTypes t1 _ = pure t1

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
checkExpr env mode mtyp@(TMapping (ValueType keytyp) (ValueType valtyp)) (U.MappingUpd p ref map) = do
    checkRef env SLHS mode ref `bindValidation` \(ValueType rtyp, tref, cnstr1) -> do
        checkEqType p mtyp rtyp
        updsc <- unzip <$> traverse (\(k,v) -> do
            kc <- checkExpr env mode keytyp k
            vc <- checkExpr env mode valtyp v
            pure $ let (k', cnstr2) = kc
                       (v', cnstr3) = vc
                   in ((k', v'), cnstr2 ++ cnstr3)) map
        pure $ let (updates, cnstr2) = updsc in
           (MappingUpd p tref keytyp valtyp updates, cnstr1 ++ concat cnstr2)
checkExpr env mode (TMapping (ValueType keytyp) (ValueType valtyp)) (U.Mapping p map) = do
    mapc <- unzip <$> traverse (\(k,v) -> do
        kc <- checkExpr env mode keytyp k
        vc <- checkExpr env mode valtyp v
        pure $ let (k', cnstr2) = kc
                   (v', cnstr3) = vc
                in ((k', v'), cnstr2 ++ cnstr3)) map
    pure $ let (map', cnstr1) = mapc in
           (Mapping p keytyp valtyp map', concat cnstr1)
-- Integer Expressions
checkExpr env mode t1@(TInteger _ _) e =
    inferExpr env mode e `bindValidation` \(TExp t2 te, cs) -> do
    case t2 of
        (TInteger _ _) ->
            if t2 `fitsIn` t1 then pure (te, cs)
            else pure (te, cs ++ [makeIntegerBoundConstraint (getPosn e) t1 te])
        TUnboundedInt -> pure (te, cs ++ [makeIntegerBoundConstraint (getPosn e) t1 te])
        _ -> typeMismatchErr (getPosn e) t1 t2
checkExpr _ _ TUnboundedInt _ = throw (nowhere, "Expected bounded integer type")
checkExpr env mode t1 e =
    let pn = getPosn e in
    inferExpr env mode e `bindValidation` \(TExp t2 te, cs) ->
    maybe (typeMismatchErr pn t1 t2) (\Refl -> pure (te, cs)) $ testEquality t1 t2

-- | Attempt to infer a type of an expression. If successful, it returns an
-- existential package of the infered typed together with the typed expression.
inferExpr :: forall t. Env -> Mode t -> U.Expr -> Err (TypedExp t, [Constraint t])
inferExpr env@Env{calldata, constructors} mode e = case e of
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
  U.EInRange _ (fromAbiType -> ValueType (TInteger _ _)) v ->
    inferExpr env mode v `bindValidation` \(TExp t te, cnstr) ->
    case t of
      TInteger _ _ -> pure (TExp TBoolean . andExps $ genInRange t te, cnstr)
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
    litBoundedType :: Integer -> TValueType AInteger
    litBoundedType v1 | v1 >= 0 && v1 <= maxUnsigned 256 = TInteger (findBoundUnsigned v1) Unsigned
                      | otherwise && v1 >= minSigned 256 && v1 <= maxSigned 256 = TInteger (findBoundSigned v1) Signed
                      | otherwise = TUnboundedInt

  U.EArray p l -> error "TODO"
    -- typedArray `bindValidation` checkAllTypes
    -- where
    --   typedArray :: Err [(Pn, TypedExp t)]
    --   typedArray = traverse (\e' -> (getPosn e',) <$> inferExpr env mode e') l
    --   checkAllTypes :: [(Pn, TypedExp t)] -> Err (TypedExp t)
    --   checkAllTypes tl = case tl of
    --     (_, TExp styp1 _ ):_ -> TExp newType <$> Array p <$> traverse (uncurry (cmpType styp1)) tl
    --       where
    --         --newShape = case shape1 of
    --         --  Atomic -> Shaped $ NonEmpty.singleton $ length l
    --         --  Shaped l' -> Shaped $ (length l) <| l'

    --         newType = TArray (length l) styp1
    --           --TArray n t -> TArray (length l : n) t

    --         cmpType :: TValueType a -> Pn -> TypedExp t -> Err (Exp a t)
    --         cmpType styp pn (TExp styp' e') =
    --           maybe (arrayTypeMismatchErr pn styp styp') (\Refl -> pure e') $ relaxedIntCheck styp styp' --if eqShape shape shape' then testEquality styp styp' else Nothing

    --     [] -> error "Empty array expressions not supported"

  -- Constructor calls
  U.ECreate p c args callvalue -> case Map.lookup c constructors of    
    Just (sig, payable, iffs) -> do
        cvc <- case (payable, callvalue) of
                (NonPayable, Just _) -> throw (p, "Constructor " <> show c <> " is not payable, but call value provided")
                (Payable, Just cvExpr) -> first Just <$> checkExpr env mode (TInteger 256 Unsigned) cvExpr
                (NonPayable, Nothing)    -> pure (Nothing, [])
                (Payable, Nothing)     -> pure (Just $ LitInt nowhere 0, [])
        argsc <- checkArgs env mode p (argToValueType <$> sig) args
        pure $ let (args', cnstr1) = argsc
                   (cv, cnstr2) = cvc
                   callcnstr = CallCnstr p args' c
                in (TExp (TContract c) (Create p c args' cv), callcnstr:cnstr1 ++ cnstr2)
    Nothing -> throw (p, "Unknown constructor " <> show c)
   -- Control
  U.EITE p e1 e2 e3 -> 
    ((,,) <$> (checkExpr env mode TBoolean e1) <*> (inferExpr env mode e2) <*> (inferExpr env mode e3))
    `bindValidation` \((te1, cnstr1), (TExp t2 te2, cnstr2), (TExp t3 te3, cnstr3)) ->
      case relaxedtestEquality t2 t3 of
        Nothing   -> typeMismatchErr p t2 t3
        Just Refl -> pure (TExp t2 (ITE p te1 te2 te3), cnstr1 ++ cnstr2 ++ cnstr3)  
  -- Environment variables
  U.EnvExp p v -> pure (TExp (ethEnv v) (IntEnv p v), [])
  -- Variable references
  U.ERef ref ->
    (\(ValueType typ, tref, cnstr) -> (TExp typ (VarRef (getPosEntry ref) typ tref), cnstr)) <$> checkRef env SRHS mode ref 
  -- Address-of operator
  U.AddrOf p e -> do
    inferExpr env mode e `bindValidation` \(TExp ty e', cnstr) -> 
      case ty of
        TContract c -> pure (TExp TAddress (Address p e'), cnstr)
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

-- | Helper to create to create a conjunction out of a list of expressions
andExps :: [Exp ABoolean t] -> Exp ABoolean t
andExps [] = LitBool nowhere True
andExps (c:cs) = foldr (And nowhere) c cs


checkArgs :: forall t. Env -> Mode t -> Pn -> [ValueType] -> [U.Expr] -> Err ([TypedExp t], [Constraint t])
checkArgs _ _ _ [] [] = pure ([], [])
checkArgs env mode pn (ValueType t:types) (e:exprs) =
    (\(e', cnstr1) (es', cnstr2) -> (TExp t e' : es', cnstr1 ++ cnstr2)) <$> checkExpr env mode t e <*> checkArgs env mode pn types exprs
    
checkArgs _ _ pn _ _ = throw (pn, "Argument length mismatch")

maxUnsigned :: Int -> Integer
maxUnsigned bits = 2 ^ bits - 1

maxSigned :: Int -> Integer
maxSigned bits = 2 ^ (bits - 1) - 1

minSigned :: Int -> Integer
minSigned bits = - (2 ^ (bits - 1))

findBoundSigned :: Integer -> Int
findBoundSigned v = go 8
  where
    go bits | v >= minSigned bits && v <= maxSigned bits = bits
            | bits >= 256 = 256
            | otherwise   = go (bits + 8)

findBoundUnsigned :: Integer -> Int
findBoundUnsigned v = go 8
  where
    go bits | 0 <= v && v <= maxUnsigned bits = bits
            | bits >= 256 = 256
            | otherwise   = go (bits + 8)