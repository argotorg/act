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
    (slocs, clocs) = partitionLocs locs
    ethEnv = ethEnvFromExp e
    calldataVars = calldataToList (calldata env)
    query = mkDefaultSMT 

    getModel solver = do
      prestate <- mapM (getStorageValue solver "" Pre) locs
      calldata <- mapM (getCalldataValue solver "" ) calldataVars
      environment <- mapM (getEnvironmentValue solver) ethEnv
      pure $ Model
        { _mprestate = prestate
        , _mpoststate = []
        , _mcalldata = ("", calldata)
        , _menvironment = environment
        , _minitargs = []
        }
      prestate <- mapM (getStorageValue solver ifaceName Pre) locs
      calldata <- mapM (getCalldataValue solver ifaceName) calldataVars
      environment <- mapM (getEnvironmentValue solver) ethEnv
      pure $ Model
        { _mprestate = prestate
        , _mpoststate = []
        , _mcalldata = ("", calldata)
        , _menvironment = environment
        , _minitargs = []
        }
mkEntailmentSMT _ = error "Internal error: only boolean constraints are supported"
  
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