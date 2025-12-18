{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE DataKinds #-}
{-# Language ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TupleSections #-}

module Act.Entailment (
  checkEntailment
) where


import Prelude hiding (GT, LT)

import Data.List
import Data.Maybe
import qualified Data.Map as M
import Data.Foldable
import Control.Monad

import Act.Syntax.TypedExplicit
import Act.SMT as SMT
import Act.Type
import Act.Print
import Act.Syntax.Timing
import Act.Error
import Act.Syntax
import Act.Traversable

import qualified EVM.Solvers as Solvers

import Debug.Trace


checkEntailment :: Solvers.Solver -> Maybe Integer -> Bool -> [Constraint Timed] -> IO (Err ())
checkEntailment solver smttimeout debug constraints = do
    let config = SMT.SMTConfig solver (fromMaybe 20000 smttimeout) debug
    smtSolver <- spawnSolver config
    let qs = mkEntailmentSMT <$> constraints
    r <- forM qs (\(smtQuery, line, msg, getModel) -> do
                           res <- checkSat smtSolver getModel smtQuery
                           pure (res, line, msg))
    sequenceA_ <$> mapM checkRes r

  where

    checkRes :: (SMT.SMTResult, Pn, String) -> IO (Err ())
    checkRes (res, pn, msg) =
        case res of
          Sat model -> pure $ throw (pn, msg <> "Counterexample:\n" <> renderString (prettyAnsi model))
          Unsat -> pure $ pure ()
          Unknown -> pure $ throw (pn, msg <> "\nSolver timeout.")
          SMT.Error _ err -> pure $ throw (pn, msg <> "Solver Error\n" <> err)

calldataToList :: M.Map Id ArgType -> [Arg]
calldataToList m = [ Arg t n | (n,t) <- M.toList m ]

mkEntailmentSMT :: Constraint Timed -> (SMTExp, Pn, String, (SolverInstance -> IO Model))
mkEntailmentSMT (BoolCnstr p str env e) =
  (query, p, str, getModel)
  where
    iff = annotate <$> preconds env
    locs = nub $ concatMap locsFromExp (e:iff)
    ethEnv = ethEnvFromExp e
    calldataVars = calldataToList (calldata env)
    query = mkDefaultSMT locs ethEnv "" calldataVars iff [] (Neg p e)

    getModel solver = do
      prestate <- mapM (getLocationValue solver "" Pre) locs
      calldata <- mapM (getCalldataValue solver "") calldataVars
      calllocs <- mapM (getLocationValue solver "" Pre) locs
      environment <- mapM (getEnvironmentValue solver) ethEnv
      pure $ Model
        { _mprestate = prestate
        , _mpoststate = []
        , _mcalldata = ("", calldata)
        , _mcalllocs = calllocs
        , _menvironment = environment
        , _minitargs = []
        }
mkEntailmentSMT (CallConstr p msg env args cid) =
  
  (query, p, str, getModel)
  
  where
    -- current preconditions
    iffs = annotate <$> preconds env

    -- called constructors preconditions. Can only refer to args and eth env.
    (calledCalldata, calledPreconds) = case M.lookup cid (constructors env) of
                        Just (Constructor _ _ preconds _) -> (calldataToList (calldata env), annotate <$> preconds)
                        Nothing -> error $ "Internal error: constructor " <> show cid <> " not found in environment."
    

    subst = M.fromList $ zip calledCalldata args




applySubstRef :: M.Map Id TypedExp -> Ref k t -> TypedExp
applySubstRef subst (CVar p t x) = 
    case M.lookup x subst of
      Just (Typed.TExp _ e) -> case e of
                                 VarRef _ _ (CVar _ _ y) -> CVar p t y
                                 _ -> CVar p t x
      Nothing -> error $ "Internal error: variable " <> show x <> " not found in substitution."
applySubstRef subst (RArrIdx p a b n) =
    case applySubstRef subst a of
      VarRef p' tv ref -> RArrIdx p ref (applySubst subst b) n
      _ -> error "Internal error: expected VarRef in array index reference substitution."
applySubstRef subst (RMapping p kt vt kvs) = error "Internal error: Calldata cannot have mapping type."
applySubstRef subst (RField p r c x) =
    case applySubstRef subst r of
      VarRef p' tv ref -> RField p ref c (applySubst subst x)
      _ -> error "TODO: expected VarRef in field reference substitution." -- TODO what if it is constructor call? Plan: evaluate the constructor call. 
applySubstRef _ (SVar _ _ _ _) = error "Internal error: storage variable found in calldata substitution."

applySubst :: M.Map Id TypedExp -> Exp a -> Exp a
applySubst subst exp = mapTerm substRefInExp exp
    where
        substRefInExp :: Exp a -> Exp a
        substRefInExp (VarRef p t ref) = case applySubstRef subst ref of
          TyExp t' e -> case testEquality t t' of
            Just Refl -> VarRef p t e
            Nothing -> error "Internal error: type mismatch in substitution."
        substRefInExp e = e 

{- 

-- | Create a query for cases
mkCaseQuery :: ([Exp ABoolean] -> Exp ABoolean) -> [Behaviour] -> (Id, SMTExp, (SolverInstance -> IO Model))
mkCaseQuery props behvs@((Behaviour _ _ (Interface ifaceName decls) _ preconds _ _ _ _):_) =
  (ifaceName, mkSMT, getModel)
  where
    locs = nub $ concatMap locsFromExp (preconds <> caseconds)
    env = concatMap ethEnvFromBehaviour behvs
    pres = mkAssert ifaceName <$> preconds
    caseconds = concatMap _caseconditions behvs

    mkSMT = SMTExp
      { _storage = concatMap (declareStorage [Pre]) locs
      , _calldata = declareArg ifaceName <$> calldataToList (calldata env)
      , _environment = declareEthEnv <$> env
      , _assertions = (mkAssert "" $ props caseconds) : pres 
      }

    getModel solver = do
      prestate <- mapM (getStorageValue solver ifaceName Pre) locs
      calldata <- mapM (getCalldataValue solver ifaceName) decls
      environment <- mapM (getEnvironmentValue solver) env
      pure $ Model
        { _mprestate = prestate
        , _mpoststate = []
        , _mcalldata = (ifaceName, calldata)
        , _menvironment = environment
        , _minitargs = []
        }
mkCaseQuery _ [] = error "Internal error: behaviours cannot be empty"    

-}