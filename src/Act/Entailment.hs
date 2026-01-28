{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE DataKinds #-}
{-# Language ScopedTypeVariables #-}
{-# LANGUAGE KindSignatures #-}

module Act.Entailment where


import Prelude hiding (GT, LT)

import Data.List
import Data.Maybe
import qualified Data.Map as M
import Data.Foldable
import Control.Monad
import Data.Type.Equality (TestEquality(..), (:~:)(..))

import Act.Syntax.TypedExplicit
import qualified Act.Syntax.Typed as Typed
import Act.SMT as SMT
import Act.Type
import Act.Print
import Act.Syntax.Timing
import Act.Error
import Act.Syntax
import Act.Traversals
import Act.Bounds

import System.IO (hPutStrLn, stderr)

import qualified EVM.Solvers as Solvers


-- | Check whether a set of constraints generated during typing is always valid
checkEntailment :: Solvers.Solver -> Maybe Integer -> Bool -> [Constraint Timed] -> IO (Err ())
checkEntailment solver smttimeout debug constraints = do
    solver' <- case solver of
          Solvers.Bitwuzla -> do
            hPutStrLn stderr "Warning: Using CVC5 solver instead of Bitwuzla for type checking."
            pure Solvers.CVC5
          s -> pure s
    let config = SMT.SMTConfig solver' (fromMaybe 20000 smttimeout) debug
    smtSolver <- spawnSolver config
    let qs = mkEntailmentSMT <$> constraints
    r <- forM qs (\(smtQuery, line, msg, model) -> do
                           -- traceM $ "Entailment SMT Query:\n" <> renderString (prettyAnsi smtQuery) <> "\n" <> msg <> "\n"          
                           res <- checkSat smtSolver model smtQuery
                           pure (res, line, msg))
    sequenceA_ <$> mapM checkRes r
  where
    checkRes :: (SMT.SMTResult, Pn, String) -> IO (Err ())
    checkRes (res, pn, msg) =
        case res of
          Sat model -> pure $ throw (pn, msg <> "\n" <> renderString (prettyAnsi model))
          Unsat -> pure $ pure ()
          Unknown -> pure $ throw (pn, msg <> "\nSolver timeout.")
          SMT.Error _ err -> pure $ throw (pn, msg <> "Solver Error\n" <> err)

-- | Convert calldata map to list of Args
calldataToList :: M.Map Id ArgType -> [Arg]
calldataToList m = [ Arg t n | (n,t) <- M.toList m ]

-- | Create an SMT query for an entailment constraint, along with a function
-- to extract a model if the solver returns `sat`
mkEntailmentSMT :: Constraint Timed -> (SMTExp, Pn, String, (SolverInstance -> IO Model))
mkEntailmentSMT (BoolCnstr p str env e) =
  (query, p, str, getModel locs calldataVars ethVars)
  where
    -- current preconditions
    iff = setPre <$> preconds env
    -- bound conditions
    bounds = mkRefsBounds locs <> mkCallDataBounds calldataVars <> mkEthEnvBounds ethVars
    -- all locations referenced in the expressions
    locs = nub $ concatMap locsFromExp (e:iff)
    -- all ethereum environment variables referenced in the expressions
    ethVars = concatMap ethEnvFromExp (e:iff)
    -- calldata variables
    calldataVars = calldataToList (calldata env)
    -- the SMT query
    query = mkDefaultSMT locs ethVars "" calldataVars (bounds <> iff) [] (Neg p e)
mkEntailmentSMT (CallCnstr p msg env args cv cid) =
--    trace ("Generating entailment SMT for constructor call to " <> show cid) $
--    trace ("With args: " <> showTypedExps args) $
--    trace ("With preconditions: " <> showExps (setPre <$> preconds env)) $
--    trace ("Query condition: " <> showExps [cond]) $
--    trace ("Query condition raw: " <> show cond) $
--    trace ("Message: " <> msg) $
  (query, p, msg, getModel locs calldataVars ethVars)

  where
    -- current preconditions
    iffs = setPre <$> preconds env
    -- bound conditions
    bounds = mkRefsBounds locs <> mkCallDataBounds calldataVars <> mkEthEnvBounds ethVars
    -- all locations referenced in the expressions
    locs = nub $ concatMap locsFromExp (cond:iffs)
    -- all ethereum environment variables referenced in the expressions
    ethVars = concatMap ethEnvFromExp (cond:iffs)
    -- calldata variables
    calldataVars = calldataToList (calldata env)
    -- constructor being called
    cnstr = fromMaybe (error $ "Internal error: constructor " <> show cid <> " not found in environment.") $ M.lookup cid (constructors env)
    -- called constructors preconditions. Can only refer to args and eth env.
    calledPreconds = setPre <$> (_cpreconditions cnstr)
    -- names of formal parameters of the called constructor
    calledCalldata = constructorArgs cnstr
    -- substitution from formal parameters to actual arguments
    subst = makeSubst args calledCalldata cv
    -- substituted preconditions of the called constructor
    cond = andExps (applySubst (constructors env) subst <$> calledPreconds)
    -- the SMT query
    query = mkDefaultSMT locs ethVars "" calldataVars (bounds <> iffs) [] (Neg p cond)

makeSubst :: [TypedExp] -> [Id] -> Maybe (Exp AInteger) -> M.Map Id TypedExp
makeSubst args cargs (Just cv) =
    M.fromList $ ("CALLVALUE", TExp (TInteger 256 Unsigned) cv) : zip cargs args
makeSubst args cargs Nothing =
    M.fromList $ ("CALLVALUE", TExp (TInteger 256 Unsigned) (LitInt nowhere 0)) : zip cargs args

constructorArgs :: Typed.Constructor t -> [Id]
constructorArgs constr = (\(Arg _ name) -> name) <$> (case _cinterface constr of Interface _ as -> as)

-- | Apply a substitution to a variable reference
applySubstRef :: Constructors -> M.Map Id TypedExp -> Ref k -> TypedExp
applySubstRef _ subst v@(CVar p at x) =
    case M.lookup x subst of
      Just te -> te
      Nothing -> case argToValueType at of
                    ValueType vt -> TExp vt (VarRef p vt v)
applySubstRef ctors subst (RArrIdx p a b n) =
    case applySubstRef ctors subst a of
      TExp t (VarRef p' tv ref) -> TExp t (VarRef p' tv (RArrIdx p ref (applySubst ctors subst b) n))
      _ -> error "Internal error: expected VarRef in array index reference substitution."
applySubstRef _ _ (RMapIdx _ _ _) = error "Internal error: Calldata cannot have mapping type."
applySubstRef ctors subst (RField p r c x) =
    case applySubstRef ctors subst r of
      TExp t (VarRef p' tv ref) -> TExp t (VarRef p' tv (RField p ref c x))
      TExp _ (Create _ c' args cv) ->
        let args' = map (applySubstTExp ctors subst) args in
        let cv' = applySubst ctors subst <$> cv in
        evalConstrCall ctors args' cv' c' x
      _ -> error "Internal error: expected VarRef or constructor call in field reference substitution."
      -- TODO: support if-then-else expressions passed as arguments to constructors
applySubstRef _ _ s@(SVar _ _ _ _) = error $ "Internal error: found storage variable reference in constructor: " <> show s

evalConstrCall :: Constructors -> [TypedExp] -> Maybe (Exp AInteger) -> Id -> Id -> TypedExp
evalConstrCall ctors args cv cid cfield = evalCases $ applySubstCase ctors subst <$> cases
  where
    -- Find the constructor in the environment
    constr = annotate <$> fromMaybe (error $ "Internal error: constructor " <> show cid <> " not found in environment.") $ M.lookup cid ctors
    -- Constructor cases
    cases = _ccases constr
    -- Constructor formal argument names
    cargs = constructorArgs constr
    -- Substitution from formal arguments to actual arguments
    subst = makeSubst args cargs cv

    -- Evaluate the cases to find the field
    evalCases :: [Ccase] -> TypedExp
    evalCases [] = error $ "Internal error: field " <> show cfield <> " not found in constructor cases."
    evalCases [Case _ _ creates] = findStorageField creates
    evalCases ((Case _ c creates):rest) =
        case findStorageField creates of
          TExp t fieldExp -> case evalCases rest of
            TExp t' restExp ->
              case testEquality t t' of
                Just Refl -> TExp t (ITE nowhere c fieldExp restExp)
                Nothing  -> error "Internal error: type mismatch in constructor field extraction."

    -- Find the field in the creates of a case
    findStorageField :: [StorageUpdate] -> TypedExp
    findStorageField [] = error $ "Internal error: field " <> show cfield <> " not found in constructor."
    findStorageField ((Update tv@VType (SVar _ _ _ x) e):upds) =
        if x == cfield then (TExp tv e) else findStorageField upds
    findStorageField (_:_) = error "Internal error: unexpected non-storage update in constructor."

-- | Apply a substitution to a typed expression
applySubstTExp :: Constructors -> M.Map Id TypedExp -> TypedExp -> TypedExp
applySubstTExp ctors subst (TExp t e) = TExp t (applySubst ctors subst e)

applySubstCase :: Constructors -> M.Map Id TypedExp -> Ccase -> Ccase
applySubstCase ctors subst (Case pn cond upds) =
    Case pn (applySubst ctors subst cond) (applySubstStorageUpd ctors subst <$> upds)

applySubstStorageUpd :: Constructors -> M.Map Id TypedExp -> StorageUpdate -> StorageUpdate
applySubstStorageUpd ctors subst (Update t r e) =
    Update t r (applySubst ctors subst e)


-- | Apply a substitution to an expression
applySubst :: Constructors -> M.Map Id TypedExp -> Exp a -> Exp a
applySubst ctors subst = mapExp substRefInExp
    where
        substRefInExp :: Exp a -> Exp a
        substRefInExp (VarRef _ t ref) = case applySubstRef ctors subst ref of
          TExp t' e -> case testEquality t t' of
            Just Refl -> e
            Nothing -> error "Internal error: type mismatch in substitution."
        substRefInExp (IntEnv _ Callvalue) = case M.lookup "CALLVALUE" subst of
          Just (TExp t e) -> case testEquality t (TInteger 256 Unsigned) of
            Just Refl -> e
            Nothing -> LitInt nowhere 0
          Nothing -> error "Internal error: CALLVALUE not found in substitution."
        substRefInExp e = e


-- | Create a model extraction function for an entailment constraint
getModel :: [TypedRef] -> [Arg] -> [EthEnv] -> SolverInstance -> IO Model
getModel locs calldataVars ethVars solver = do
    prestate <- mapM (getLocationValue solver "" Pre) locs
    callvars <- mapM (getCalldataValue solver "") calldataVars
    calllocs <- mapM (getLocationValue solver "" Pre) locs
    environment <- mapM (getEnvironmentValue solver) ethVars
    pure $ Model
        { _mprestate = prestate
        , _mpoststate = []
        , _mcalldata = ("", callvars)
        , _mcalllocs = calllocs
        , _menvironment = environment
        , _minitargs = []
        }



-- For debugging purposes

showCnstr :: Constraint Timed -> String
showCnstr (BoolCnstr _ msg env e) = "Boolean constraint:\n" <> 
  msg <> "\n"
    <> "Preconditions: \n" <> showExps (setPre <$> preconds env) <> "\n"
    <> "Expression: " <> prettyExp e <> "\n"
showCnstr (CallCnstr _ msg _ _ _ _) = "Call constraint: " <> msg
    
showCnstrs :: [Constraint Timed] -> String
showCnstrs cs = intercalate "\n\n" (map showCnstr cs)

showExps :: [Exp a] -> String
showExps exps = intercalate "\n" (map prettyExp exps)

showTypedExps :: [TypedExp] -> String
showTypedExps exps = intercalate "\n" (map (\(TExp _ e) -> prettyExp e) exps)