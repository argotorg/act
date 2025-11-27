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
import Control.Monad.Accum (MonadAccum(add))


type Err = Error String

-- | A map containing the interfaces of all available constructors together with their preconditions.
type Constructors = Map Id ([ArgType], [Exp ABoolean Untimed])

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

typecheck :: U.Act -> Err Act
typecheck (U.Main contracts) = 
    uncurry Act <*> typecheckContracts' contracts
    

typecheckContracts' :: [U.Contract] -> Err (StorageTyping, [Contract])
typecheckContracts' = 
    (\(env, constracts) -> (storage env, constracts)) <*> typecheckContracts emptyEnv

typecheckContracts :: Env -> [U.Contract] -> Err (StorageTyping, [Contract])
typecheckContracts env [] = pure (env, [])
typecheckContracts env ((U.Contract cnstr behvs):cs) =
    typecheckConstructor env cnstr `bindValidation` \(env', cnstr') ->
    typecheckBehaviors env' behvs `bindValidation` \(env'', behvs') ->
    typecheckContracts env'' cs `bindValidation` \(env''', cs') ->
    pure (env''', (Contact cnstr' behvs') : cs') 

mkConstrEnv :: Id -> Env -> Env
mkConstrEnv cid iface env = env { contract = cid , storage = mempty, calldata =  mkCalldata iface }

mkCalldata :: [Decl] -> Env -> Env
mkCalldata decls env = env{ calldata = abiVars }
  where
   abiVars = Map.fromList $ map (\(Decl typ var) -> (var, typ)) decls

typecheckConstructor :: Env -> U.Constructor -> Err (Constructor, Env)
typecheckConstructor env (U.Constructor posn cid (Interface _ params) iffs cases posts invs) = do
    traverse_ (checkParams env') decls
    checkConstrName cid env
    let env' = mkConstrEnv cid env
    iffs' <- checkExpr env TBoolean iffs
    (storageType, cases) <- concat <$> checkConstrCases env' cases    
    ensures <- traverse (checkExpr env' TBoolean) posts
    invs' <- fmap (Invariant contract [] [] . PredUntimed) <$> traverse (checkExpr env' TBoolean) invs
    env' <- addConstructorStorage env storageType 
    pure (Constructor contract (Interface contract decls) ptrs iffs' ensures invs' stateUpdates, env')
    where
        addConstructorStorage :: Env -> Map Id (ValueType, Integer) -> Err Env
        addConstructorStorage env storageType = 
            pure env { storage = Map.insert cid storageType storage }

        checkConstrName :: Id -> Env -> Err ()
        checkConstrName cid Env{constructors} =
            case Map.lookup cid constructors of
                Just _ -> throw (posn, "Constructor " <> cid <> " is already defined")
                Nothing -> pure ()

checkParams :: Env -> U.Decl -> Err ()
checkParams Env{storage} (Decl (ContractArg p c) _) =
  case Map.lookup c storage of
    Nothing -> throw (p, "Contract " <> c <> " is not a valid contract type")
    Just _ -> pure ()
-- TODO check that abi types are valid    
checkParams _ _ = pure ()

typecheckConstrCases :: Env -> [U.Case U.Creates] -> Err (Map Id (ValueType, Integer), Cases [StorageUpdate])
typecheckConstrCases env cases = do
  -- TODO check case consistency
  cases' <- for cases $ \(U.Case p cond assigns) -> do
    cond' <- checkExpr env TBoolean cond
    storageUpdates <- concat <$> traverse (checkAssign env) assigns
    pure $ Case p cond' storageUpdates
  storageTyping <- checkStorageTyping cases
  pure (storageTyping, cases')
  where
    checkStorageTyping :: [U.Case U.Creates] -> Map Id (ValueType, Integer)
    checkStorageTyping [] = mempty
    checkStorageTyping ((U.Case p cond assigns):cases) =
        let typing = makeStorageTyping assigns 0 in
        consistentStorageTyping typing cases
        M.fromList typing
    
    -- make the storage typing from a list of assignments
    makeStorageTyping :: [U.Assign] ->  [(Id, (ValueType, Integer))]
    makeStorageTyping [] _ = []
    makeStorageTyping ((U.StorageVar _ typ name):rest) slot = (name, (typ, slot)):makeStorageTyping rest (slot + 1)

    -- check that the storage typing is the same across all cases
    consistentStorageTyping :: Map Id (ValueType, Integer) -> [U.Case U.Creates] -> Err ()
    consistentStorageTyping _ [] = pure ()
    consistentStorageTyping typing ((U.Case p _ assigns):cases) =
        let typing' = makeStorageTyping assigns 0 in
        consistentStorageTyping typing cases *>
        assert (p, "Inconsistent storage typing in constructor cases")

checkBehaviours :: Env -> [U.Transition] -> Err [Behaviour]
checkBehaviours env _ [] = pure (storage env, [])
checkBehaviours env names (b:bs) = do
    checkBehvName b bs
    b' <- checkBehaviour env b
    bs' <- checkBehaviours env bs
    pure $ b':bs'

    where
        checkBehvName :: U.Transition -> [U.Transition] -> Err ()
        checkBehvName (U.Transition pn name _ _ _ _ _) bs =
            case find (\(U.Transition _ n _ _ _ _ _) -> n == name) bs of
                Just _ -> throw (pn, "Behaviour " <> name <> "for contract " <> contract <> " is already defined")
                Nothing -> pure ()


checkBehavior :: Env -> U.Transition -> Err Behaviour
checkBehavior env@Env{contract} (U.Transition posn name _ iface@(Interface _ decls) iffs cases posts) = do
    traverse_ (checkDecl env) decls
    let env' = addCalddata iface env
    iffs' <- checkIffs env iffs
    -- TODO check case consistency
    cases' <- concat <$> traverse (checkBehvCase env') cases
    ensures <- traverse (checkExpr env TBoolean) posts
    pure $ Behaviour name contract iface iffs' cases' ensures storageType


checkBehvCase :: Env -> U.Case (U.StorageUpdates, Maybe U.Expr) -> Err ([Exp ABoolean Untimed], ([StorageUpdate], Maybe (TypedExp Timed)))
checkBehvCase env (U.Case p cond (updates, mret)) = do
    cond' <- checkExpr env TBoolean cond
    storageUpdates <- concat <$> traverse (checkStorageUpdate env) updates
    mret' <- checkTypedExpr env Timed <$> mret
    pure (cond', storageUpdates, mret')


checkAssign :: Env -> U.Assign -> Err [StorageUpdate]
checkAssign env (U.StorageVar p typ var, expr) = do
    validSlotType env p typ
    expr' <- checkExpr env typ expr
    pure [Update (RVar p var) expr']
  where
    validSlotType :: Env -> Pn -> TValueType a -> Err ()
    validSlotType env p (TInteger size _) =
      when (size `notElem` [8,16,32,64,128,256]) $
        throw (p, "Invalid integer size: " <> show size)
    validSlotType env p (TContract c) =
      case Map.lookup c (theirs env) of
        Just _ -> pure ()
        Nothing -> throw (p, "Contract " <> c <> " is not a valid contract type")
    validSlotType _ _ _ = pure ()

checkStorageUpdate :: Env -> U.StorageUpdate -> Err StorageUpdate
checkStorageUpdate env (U.Update ref expr) = do
    (tref, typ) <- checkRef env SStorage ref
    expr' <- checkExpr env typ expr
    pure $ Update tref expr'

-- | Environment with globally available variables.
ethEnv :: EthEnv -> TValueType AInteger
ethEnv Callvalue = TInteger 256 Unsigned
ethEnv Caller    = TAddress
ethEnv This      = TAddress
ethEnv Origin    = TAddress


-- inferRefType :: Env -> U.Ref -> Err TypedRef
-- inferRefType env ref = do 
--   kind <- inferKind env ref
--   (typ, tref) <- checkRef env kind ref
--   pure $ TRef typ tref  
--   where
--     inferKind :: Env -> U.Ref -> Err SRefKind
--     inferKind Env{calldata} (U.RVar p name) = 
--       case Map.lookup name calldata of
--         Just _ -> pure S
--         Nothing -> pure SStorage
--     inferKind env (U.RIndex p en _) =
--       inferKind env en
--     inferKind env (U.RField p en _) =
--       inferKind env en

checkRef :: forall t k. Typeable t => Env -> SRefKind k -> U.Ref -> Err (ValueType, Ref k t)
checkRef Env{contract, calldata, storage} kind (U.RVar p name) = 
    case M.lookup name calldata of
      Just typ -> case kind of 
        SLHS -> throw (p, "Cannot use calldata variable " <> show name <> " as LHS reference")
        SRHS -> pure (fromAbiType' typ, CVar p typ name)
      Nothing -> case M.lookup contract storage of
        Just storageTyping -> case M.lookup name storageTyping of
            Just (typ, _) -> pure (typ, SVar p contract name)
            Nothing -> throw (p, "Unbound variable " <> show name)
        Nothing -> throw (nowhere, "Contract " <> contract <> " undefined") -- unreachable
checkRef env kind (U.RIndex p en args) =
  checkRef env kind en `bindValidation` \(styp, ref) -> case styp of
    TArray len typ -> 
        checkArrayIxs env p args (toList len) `bindValidation` \ixs ->
        pure (typ, RArrIdx p ref typ ixs)
    TMapping keytyp valtyp ->
        checkArgs env p (NonEmpty.toList keytyp) args `bindValidation` \ixs ->
        case kind of
            SLHS -> throw (p, "Cannot use mapping indexing as LHS reference")
            SRHS -> pure (valtyp, RMapIdx p ref valtyp ixs)
    _ -> throw (p, "An indexed reference should have an array or mapping type" <> show en)
checkRef env kind (U.RField p en x) =
  checkRef env kind en `bindValidation` \(styp, ref) -> case styp of
    TContract c -> case Map.lookup c (theirs env) of
      Just cenv -> case Map.lookup x cenv of
        Just (typ, _) -> pure (typ, RField p ref c x)
        Nothing -> throw (p, "Contract " <> c <> " does not have field " <> x)
      Nothing -> error $ "Internal error: Invalid contract type " <> show c
    _ -> throw (p, "Reference should have a contract type" <> show en)


-- | If an `inrange e` predicate appears in the source code, then the inrange
-- predicate is propagated to all subexpressions of `e`. 
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

defaultInteger :: TValueType AInteger
defaultInteger = TInteger 256 Signed

defaultUInteger :: TValueType AInteger
defaultUInteger = TInteger 256 Unsigned


relaxedIntCheck :: TValueType a -> TValueType b -> Maybe (a :~: b)
relaxedIntCheck (TInteger _ _) (TInteger _ _) = Just Refl
relaxedIntCheck (TArray n1 t1) (TArray n2 t2) | n1 == n2 = (\Refl -> Just Refl) =<< relaxedIntCheck t1 t2
relaxedIntCheck t1 t2 = testEquality t1 t2

-- | Attempt to construct a `TypedExp` whose type matches the supplied `ValueType`.
-- The target timing parameter will be whatever is required by the caller.
checkExprVType :: forall t. Typeable t => Env -> U.Expr -> ValueType -> Err (TypedExp t)
checkExprVType env e (ValueType vt) = TExp vt <$> checkExpr env vt e


-- | Check if the given expression can be typed with the given type
checkExpr :: forall t a. Typeable t => Env -> TValueType a -> U.Expr -> Err (Exp a t)
checkExpr env t1 e =
    -- No idea why type annotation is required here
    (inferExpr env e :: Err (TypedExp t)) `bindValidation` (\(TExp t2 te) ->
    -- TODO: when integer types will always be infered to be `defaultInteger`, so mismatch is
    -- certain for any other type. Implement conversion, and probably check validity through SMT
    -- under the preconditions/case conditions?
    maybe (maybeCast (getPosn e) t1 t2) (\Refl -> pure te) $ relaxedIntCheck t1 t2)
    where
      maybeCast :: Pn -> TValueType a -> TValueType b -> Exp b t -> Err (Exp a t)
      maybeCast pn TInteger (TContract c) te = pure $ Address pn c te --TODO: is pn correct here?
      -- maybeCast _ (SSArray _) s1' (SSArray _) s2 _ | s1' == s2 = -- TODO: cast of whole array of contracts?
      maybeCast pn t1' t2 _ = typeMismatchErr pn t1' t2

-- | Attempt to infer a type of an expression. If successful returns an
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
  U.ECreate p c args callvalue -> case Map.lookup c constructors of
    Just (sig, _iffs) -> do -- TODO check preconditions
      cv <- traverse (checkExpr env (TInteger 256 Unsigned)) callvalue
      args' <- checkArgs env p sig args
      pure $ TExp (TContract c) (Create p c args' cv)

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
  U.ERef ref -> do 
    (typ, tref) <- checkRef env SRHS ref
    pure $ TExp typ $ VarRef (getPosEntry ref) Timed SCalldata (Item typ tref)

  U.AddrOf p e -> do
    inferExpr env TContract e `bindValidation` \case 
      TExp (TContract c) e' -> pure $ TExp TAddress (Address p c e')
      TExp t _ -> throw (p, "Expression of type " <> show t <> " cannot be converted to address")

  U.Mapping p [] -> throw (p, "Cannot create empty mapping")

  U.Mapping p ((key,val):map) -> do
    TExp keytyp key' <- inferExpr env key
    TExp valtyp val' <- inferExpr env val
    rest <- traverse (\(k,v) -> do
        k' <- checkExpr env keytyp k
        v' <- checkExpr env valtyp v
        pure (k', v')) map
    pure $ TExp (TMapping (ValueType keytyp) (ValueType valtyp)) (Mapping p keytyp valtyp ((key', val') : rest))

  U.MappingUpd p ref map -> do
    (styp, tref) <- checkRef env SLHS ref    
    case styp of
      TMapping keytyp valtyp -> do
        updates <- traverse (\(k,v) -> do
            k' <- checkExpr env keytyp k
            v' <- checkExpr env valtyp v
            pure (k', v')) map
        pure $ TExp styp (MappingUpd p tref keytyp valtyp updates)
      _ -> throw (p, "Mapping update applied to non-mapping type" <> show ref)
    
  --  
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

    -- Check that an expression is typed with the right timing
    checkTime :: forall t0. Typeable t0 => Pn -> Err (TypedExp t0 -> TypedExp t)
    checkTime pn = case eqT @t @t0 of
      Just Refl -> pure id
      Nothing   -> throw (pn, (tail . show $ typeRep @t) <> " variable needed here")

-- | Helper to create to create a conjunction out of a list of expressions
andExps :: [Exp ABoolean t] -> Exp ABoolean t
andExps [] = LitBool nowhere True
andExps (c:cs) = foldr (And nowhere) c cs


checkArgs :: forall t. Typeable t => Env -> Pn -> [ValueType] -> [U.Expr] -> Err [TypedExp t]
checkArgs env pn [] [] = pure []
checkArgs env pn (t:types) (e:exprs) = do
    e' <- checkExpr env (fromAbiType' t) e
    es' <- checkArgs env pn types exprs
    pure (TExp (fromAbiType' t) e' : es')
checkArgs env pn _ _ = throw (pn, "Argument length mismatch")

-- | Checks that there are as many expressions as expected by the array,
-- and checks that each one of them can be typed into Integer
checkArrayIxs :: forall t. Typeable t => Env -> Pn -> [U.Expr] -> [Int] -> Err [(TypedExp t,Int)]
checkArrayIxs env pn exprs ixsBounds = if length exprs > length ixsBounds
                              then throw (pn, "Index mismatch for entry")
                              else traverse check (zip exprs ixsBounds)
  where
    check (e,i) = checkExpr env defaultUInteger e `bindValidation` (pure . (\e' -> (TExp defaultUInteger e', i)))
