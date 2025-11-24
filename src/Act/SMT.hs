{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# Language RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}

module Act.SMT (
  Solver(..),
  SMTConfig(..),
  Query(..),
  SMTResult(..),
  SMTExp(..),
  SolverInstance(..),
  Model(..),
  Transition(..),
  SMT2,
  spawnSolver,
  stopSolver,
  sendLines,
  runQuery,
  mkDefaultSMT,
  mkPostconditionQueries,
  mkPostconditionQueriesBehv,
  mkInvariantQueries,
  target,
  getQueryContract,
  isFail,
  isPass,
  ifExists,
  getBehvName,
  identifier,
  getSMT,
  checkSat,
  getCtorModel,
  getPostconditionModel,
  mkAssert,
  declareInitialLocation,
  declareLocation,
  declareArg,
  declareEthEnv,
  getLocationValue,
  getCalldataValue,
  getEnvironmentValue,
  mkEqualityAssertion,
) where

import Prelude hiding (GT, LT)

import Data.Containers.ListUtils (nubOrd)
import System.Process (createProcess, cleanupProcess, proc, ProcessHandle, std_in, std_out, std_err, StdStream(..))
import Text.Regex.TDFA hiding (empty)
import Prettyprinter hiding (Doc)

import Control.Applicative ((<|>))
import Control.Monad.Reader
import Control.Monad

import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe
import Data.List
import GHC.IO.Handle (Handle, hGetLine, hPutStr, hFlush)
import Data.ByteString.UTF8 (fromString)

import Act.Syntax
import Act.Syntax.TypedExplicit hiding (array)

import Act.Print
import Act.Type (globalEnv)

import EVM.Solvers (Solver(..))
import Data.Type.Equality ((:~:)(..), testEquality)
import Debug.Trace

--- ** Data ** ---


data SMTConfig = SMTConfig
  { _solver :: Solver
  , _timeout :: Integer
  , _debug :: Bool
  }

type SMT2 = String

-- | The context is a `Reader` monad which allows us to read
-- the name of the current interface.
type Ctx = Reader Id

-- | Specify the name to use as the current interface when creating SMT-code.
withInterface :: Id -> Ctx SMT2 -> SMT2
withInterface = flip runReader

-- | An SMTExp is a structured representation of an SMT Expression
--   The _storage, _calldata, and _environment fields hold variable declarations
--   The _assertions field holds the various constraints that should be satisfied
data SMTExp = SMTExp
  { _storage :: [SMT2]
  , _calldata :: [SMT2]
  , _environment :: [SMT2]
  , _assertions :: [SMT2]
  }
  deriving (Show)

instance PrettyAnsi SMTExp where
  prettyAnsi e = vsep [storage, calldata, environment, assertions]
    where
      storage = pretty ";STORAGE:" <$$> (vsep . (fmap pretty) . nubOrd . _storage $ e) <> line
      calldata = pretty ";CALLDATA:" <$$> (vsep . (fmap pretty) . nubOrd . _calldata $ e) <> line
      environment = pretty ";ENVIRONMENT" <$$> (vsep . (fmap pretty) . nubOrd . _environment $ e) <> line
      assertions = pretty ";ASSERTIONS:" <$$> (vsep . (fmap pretty) . nubOrd . _assertions $ e) <> line

data Transition
  = Behv Behaviour
  | Ctor Constructor
  deriving (Show)

-- | A Query is a structured representation of an SMT query for an individual
--   expression, along with the metadata needed to extract a model from a satisfiable query
data Query
  = Postcondition Transition (Exp ABoolean) SMTExp
  | Inv Invariant (Constructor, SMTExp) [(Behaviour, SMTExp)]
  deriving (Show)

data SMTResult
  = Sat Model
  | Unsat
  | Unknown
  | Error Int String
  deriving (Show)

-- | An assignment of concrete values to symbolic variables structured in a way
--   to allow for easy pretty printing. The LHS of each pair is the symbolic
--   variable, and the RHS is the concrete value assigned to that variable in the
--   counterexample
data Model = Model
  { _mprestate :: [(Location, TypedExp)]
  , _mpoststate :: [(Location, TypedExp)]
  , _mcalldata :: (String, [(Decl, TypedExp)])
  , _mcalllocs :: [(Location, TypedExp)]
  , _menvironment :: [(EthEnv, TypedExp)]
  -- invariants always have access to the constructor context
  , _minitargs :: [(Decl, TypedExp)]
  }
  deriving (Show)

instance PrettyAnsi Model where
  prettyAnsi (Model prestate poststate (ifaceName, args) _ environment initargs) =
    (underline . pretty $ "counterexample:") <$$> line
      <> (indent 2
        (    calldata'
        <$$> ifExists environment (line <> environment' <> line)
        <$$> storage
        <$$> ifExists initargs (line <> initargs')
        ))
    where
      calldata' = pretty "calldata:" <$$> line <> (indent 2 $ formatSig ifaceName args)
      environment' = pretty "environment:" <$$> line <> (indent 2 . vsep $ fmap formatEnvironment environment)
      storage = pretty "storage:" <$$> (indent 2 . vsep $ [ifExists prestate (line <> prestate'), ifExists poststate (line <> poststate')])
      initargs' = pretty "constructor arguments:" <$$> line <> (indent 2 $ formatSig "constructor" initargs)

      prestate' = pretty "prestate:" <$$> line <> (indent 2 . vsep $ fmap formatStorage prestate) <> line
      poststate' = pretty "poststate:" <$$> line <> (indent 2 . vsep $ fmap formatStorage poststate)

      formatSig iface cd = pretty iface <> (encloseSep lparen rparen (pretty ", ") $ fmap formatCalldata cd)
      formatCalldata (Decl _ name, val) = pretty $ name <> " = " <> prettyTypedExp val
      formatEnvironment (env, val) = pretty $ prettyEnv env <> " = " <> prettyTypedExp val
      formatStorage (loc, val) = pretty $ prettyLocation loc <> " = " <> prettyTypedExp val


data SolverInstance = SolverInstance
  { _type :: Solver
  , _stdin :: Handle
  , _stdout :: Handle
  , _stderr :: Handle
  , _process :: ProcessHandle
  }


--- ** Analysis Passes ** ---

-- | Produces an SMT expression in a format that services most SMT passes.
mkDefaultSMT :: Bool -> [Location] -> [Location] -> [EthEnv] -> Id -> [Decl] -> [Exp ABoolean] -> [Exp ABoolean] -> [StorageUpdate] -> Exp ABoolean -> SMTExp
mkDefaultSMT isCtor activeSLocs activeCLocs envs ifaceName decls preconds extraconds stateUpdates = mksmt
  where
    -- If called for a constructor, declare only the post-state for local storage,
    -- and both states for other locations.
    -- Otherwise, when called for a behaviour, declare declare both states for all locations.
    storage = if isCtor
      then let (localSLocs, nonlocalSLocs) = partition isLocalLoc (activeSLocs) in nub $
        concatMap (declareInitialLocation ifaceName) localSLocs <> concatMap (declareLocation ifaceName) nonlocalSLocs
      else nub $ concatMap (declareLocation ifaceName) activeSLocs

    -- Declare calldata arguments and locations, and environmental variables
    ifaceArgs = declareArg ifaceName <$> decls
    activeArgs = concatMap (declareLocation ifaceName) activeCLocs
    args = nub ifaceArgs <> activeArgs

    env = declareEthEnv <$> envs

    -- Collect all locations not tautologically equal to the updated locations,
    -- to encode the conditions under which they stay constant.
    -- For constructors this should involve only locations not from local storage.
    updatedLocs = locFromUpdate <$> stateUpdates
    maybeConstSLocs = let unUpdated = (nub activeSLocs) \\ updatedLocs in
      if isCtor then filter (not . isLocalLoc) unUpdated else unUpdated

    -- Constraints
    pres = mkAssert ifaceName <$> preconds <> extraconds
    updates = encodeUpdate ifaceName <$> stateUpdates
    constants = encodeConstant ifaceName updatedLocs maybeConstSLocs

    mksmt e = SMTExp
      { _storage = storage
      , _calldata = args
      , _environment = env
      , _assertions = [mkAssert ifaceName e] <> pres <> updates <> constants
      }


-- | For each postcondition in the claim we construct a query that:
--    - Asserts that the preconditions hold
--    - Asserts that storage has been updated according to the rewrites in the behaviour
--    - Asserts that the postcondition cannot be reached
--   If this query is unsatisfiable, then there exists no case where the postcondition can be violated.
mkPostconditionQueries :: Act -> [Query]
mkPostconditionQueries (Act _ contr) = concatMap mkPostconditionQueriesContract contr
  where
    mkPostconditionQueriesContract (Contract constr behvs) =
      mkPostconditionQueriesConstr constr <> concatMap mkPostconditionQueriesBehv behvs

mkPostconditionQueriesBehv :: Behaviour -> [Query]
mkPostconditionQueriesBehv behv@(Behaviour _ _ (Interface ifaceName decls) _ preconds caseconds postconds stateUpdates _) =
    mkQuery <$> postconds
  where
    activeLocs = locsFromBehaviour behv
    (activeSLocs, activeCLocs) = partitionLocs activeLocs
    envs = ethEnvFromBehaviour behv
    mksmt e = mkDefaultSMT False activeSLocs activeCLocs envs ifaceName decls preconds caseconds stateUpdates (Neg nowhere e)
    mkQuery e = Postcondition (Behv behv) e (mksmt e)

mkPostconditionQueriesConstr :: Constructor -> [Query]
mkPostconditionQueriesConstr constructor@(Constructor _ (Interface ifaceName decls) _ preconds postconds _ initialStorage) = mkQuery <$> postconds
  where
    activeLocs = locsFromConstructor constructor
    (activeSLocs, activeCLocs) = partitionLocs activeLocs
    envs = ethEnvFromConstructor constructor
    mksmt e = mkDefaultSMT True activeSLocs activeCLocs envs ifaceName decls preconds [] initialStorage (Neg nowhere e)
    mkQuery e = Postcondition (Ctor constructor) e (mksmt e)

-- | For each invariant in the list of input claims, we first gather all the
--   specs relevant to that invariant (i.e. the constructor for that contract,
--   and all passing behaviours for that contract).
--
--   For the constructor we build a query that:
--     - Asserts that all preconditions hold
--     - Asserts that external storage has been updated according to the spec
--     - Asserts that internal storage values have the value given in the creates block
--     - Asserts that the invariant does not hold over the poststate
--
--   For the behaviours, we build a query that:
--     - Asserts that the invariant holds over the prestate
--     - Asserts that all preconditions hold
--     - Asserts that storage has been updated according to the spec
--     - Asserts that the invariant does not hold over the poststate
--
--   If all of the queries return `unsat` then we have an inductive proof that
--   the invariant holds for all possible contract states.
mkInvariantQueries :: Act -> [Query]
mkInvariantQueries (Act _ contracts) = fmap mkQuery gathered
  where
    mkQuery (inv, ctor, behvs) = Inv inv (mkInit inv ctor) (fmap (mkBehv inv ctor) behvs)
    gathered = concatMap getInvariants contracts

    getInvariants (Contract (c@Constructor{..}) behvs) = fmap (, c, behvs) _invariants

    mkInit :: Invariant -> Constructor -> (Constructor, SMTExp)
    mkInit (Invariant _ invConds _ (PredTimed _ invPost)) ctor@(Constructor _ (Interface ifaceName decls) _ preconds _ _ initialStorage) = (ctor, mksmt invPost)
      where
        activeLocs = locsFromConstructor ctor
        (activeSLocs, activeCLocs) = partitionLocs activeLocs
        envs = ethEnvFromConstructor ctor
        mksmt e = mkDefaultSMT True activeSLocs activeCLocs envs ifaceName decls preconds invConds initialStorage (Neg nowhere e)

    mkBehv :: Invariant -> Constructor -> Behaviour -> (Behaviour, SMTExp)
    mkBehv inv@(Invariant _ invConds invStorageBounds (PredTimed invPre invPost)) ctor behv = (behv, smt)
      where

        (Interface ctorIface ctorDecls) = _cinterface ctor
        (Interface behvIface behvDecls) = _interface behv


        -- declare vars
        invEnv = declareEthEnv <$> ethEnvFromExp invPre
        behvEnv = declareEthEnv <$> ethEnvFromBehaviour behv
        initArgs = declareArg ctorIface <$> ctorDecls
        behvArgs = declareArg behvIface <$> behvDecls
        activeLocs = nub $ locsFromBehaviour behv <> locsFromInvariant inv
        (activeSLocs, activeCLocs) = partitionLocs activeLocs
        storage = concatMap (declareLocation behvIface) activeSLocs
        activeArgs = concatMap (declareLocation ctorIface) activeCLocs
        args = nub initArgs <> behvArgs <> activeArgs
        -- storage locs that are mentioned but not explictly updated (i.e., constant)
        updatedLocs = fmap locFromUpdate (_stateUpdates behv)
        constLocs = (nub activeSLocs) \\ updatedLocs

        -- constraints
        preInv = mkAssert ctorIface invPre
        postInv = mkAssert ctorIface . Neg nowhere $ invPost
        behvConds = mkAssert behvIface <$> _preconditions behv <> _caseconditions behv
        invConds' = mkAssert ctorIface <$> invConds <> invStorageBounds
        constants = encodeConstant behvIface updatedLocs constLocs
        updates = encodeUpdate behvIface <$> _stateUpdates behv

        smt = SMTExp
          { _storage = storage
          , _calldata = args
          , _environment = invEnv <> behvEnv
          , _assertions = [preInv, postInv] <> behvConds <> invConds' <> constants <> updates
          }


--- ** Solver Interaction ** ---


-- | Checks the satisfiability of all smt expressions contained with a query, and returns the results as a list
runQuery :: SolverInstance -> Query -> IO (Query, [SMTResult])
runQuery solver query@(Postcondition trans _ smt) = do
  res <- checkSat solver (getPostconditionModel trans) smt
  pure (query, [res])
runQuery solver query@(Inv (Invariant _ _ _ predicate) (ctor, ctorSMT) behvs) = do
  ctorRes <- runCtor
  behvRes <- mapM runBehv behvs
  pure (query, ctorRes : behvRes)
  where
    runCtor = checkSat solver (getInvariantModel predicate ctor Nothing) ctorSMT
    runBehv (b, smt) = checkSat solver (getInvariantModel predicate ctor (Just b)) smt

-- | Checks the satisfiability of a single SMT expression, and uses the
-- provided `modelFn` to extract a model if the solver returns `sat`
checkSat :: SolverInstance -> (SolverInstance -> IO Model) -> SMTExp -> IO SMTResult
checkSat solver modelFn smt = do
  -- render (pretty smt)
  err <- sendLines solver ("(reset)" : (lines . show . prettyAnsi $ smt))
  case err of
    Nothing -> do
      sat <- sendCommand solver "(check-sat)"
      case sat of
        "sat" -> Sat <$> modelFn solver
        "unsat" -> pure Unsat
        "timeout" -> pure Unknown
        "unknown" -> pure Unknown
        _ -> pure $ Error 0 $ "Unable to parse solver output: " <> sat
    Just msg -> do
      pure $ Error 0 msg

-- | Global settings applied directly after each solver instance is spawned
smtPreamble :: [SMT2]
smtPreamble = [ "(set-logic ALL)" ]

-- | Arguments used when spawing a solver instance
solverArgs :: SMTConfig -> [String]
solverArgs (SMTConfig solver timeout _) = case solver of
  Z3 ->
    [ "-in"
    , "-t:" <> show timeout]
  CVC5 ->
    [ "--lang=smt"
    , "--interactive"
    , "--produce-models"
    , "--print-success"
    , "--arrays-exp"
    , "--tlimit-per=" <> show timeout]
  Bitwuzla ->
    [ "--lang=smt2"
    , "--produce-models"
    , "--time-limit-per=" <> show timeout
    , "--bv-solver=preprop"
    ]
  _ -> error "Unsupported solver"

-- | Spawns a solver instance, and sets the various global config options that we use for our queries
spawnSolver :: SMTConfig -> IO SolverInstance
spawnSolver config@(SMTConfig solver _ _) = do
  let cmd = (proc (show solver) (solverArgs config)) { std_in = CreatePipe, std_out = CreatePipe, std_err = CreatePipe }
  (Just stdin, Just stdout, Just stderr, process) <- createProcess cmd
  let solverInstance = SolverInstance solver stdin stdout stderr process

  _ <- sendCommand solverInstance "(set-option :print-success true)"
  err <- sendLines solverInstance smtPreamble
  case err of
    Nothing -> pure solverInstance
    Just msg -> error $ "could not spawn solver: " <> msg

-- | Cleanly shutdown a running solver instnace
stopSolver :: SolverInstance -> IO ()
stopSolver (SolverInstance _ stdin stdout stderr process) = cleanupProcess (Just stdin, Just stdout, Just stderr, process)

-- | Sends a list of commands to the solver. Returns the first error, if there was one.
sendLines :: SolverInstance -> [SMT2] -> IO (Maybe String)
sendLines solver smt = case smt of
  [] -> pure Nothing
  hd : tl -> do
    suc <- sendCommand solver hd
    if suc == "success"
    then sendLines solver tl
    else pure (Just suc)

-- | Sends a single command to the solver, returns the first available line from the output buffer
sendCommand :: SolverInstance -> SMT2 -> IO String
sendCommand (SolverInstance _ stdin stdout _ _) cmd =
  if null cmd || ";" `isPrefixOf` cmd then pure "success" -- blank lines and comments do not produce any output from the solver
  else do
    hPutStr stdin (cmd <> "\n")
    --traceM cmd
    hFlush stdin
    hGetLine stdout


--- ** Model Extraction ** ---


-- | Extracts an assignment of values for the variables in the given
-- transition. Assumes that a postcondition query for the given transition has
-- previously been checked in the given solver instance.
getPostconditionModel :: Transition -> SolverInstance -> IO Model
getPostconditionModel (Ctor ctor) solver = getCtorModel ctor solver
getPostconditionModel (Behv behv) solver = do
  let locs = locsFromBehaviour behv
      (slocs, clocs) = partitionLocs locs
      env = ethEnvFromBehaviour behv
      Interface ifaceName decls = _interface behv
  prestate <- mapM (getLocationValue solver ifaceName Pre) slocs
  poststate <- mapM (getLocationValue solver ifaceName Post) slocs
  calldata <- mapM (getCalldataValue solver ifaceName) decls
  calllocs <- mapM (getLocationValue solver ifaceName Pre) clocs -- Pre will be ignored in all calllocs
  environment <- mapM (getEnvironmentValue solver) env
  pure $ Model
    { _mprestate = prestate
    , _mpoststate = poststate
    , _mcalldata = (ifaceName, calldata)
    , _mcalllocs = calllocs
    , _menvironment = environment
    , _minitargs = []
    }

-- | Extracts an assignment of values for the variables in the given
-- transition. Assumes that an invariant query has previously been checked
-- in the given solver instance.
getInvariantModel :: InvariantPred -> Constructor -> Maybe Behaviour -> SolverInstance -> IO Model
getInvariantModel _ ctor Nothing solver = getCtorModel ctor solver
getInvariantModel predicate ctor (Just behv) solver = do
  let locs = nub $ locsFromBehaviour behv <> locsFromExp (invExp predicate)
      (slocs, clocs) = partitionLocs locs
      env = nub $ ethEnvFromBehaviour behv <> ethEnvFromExp (invExp predicate)
      Interface behvIface behvDecls = _interface behv
      Interface ctorIface ctorDecls = _cinterface ctor
  -- TODO: v ugly to ignore the ifaceName here, but it's safe...
  prestate <- mapM (getLocationValue solver "" Pre) slocs
  poststate <- mapM (getLocationValue solver "" Post) slocs
  behvCalldata <- mapM (getCalldataValue solver behvIface) behvDecls
  ctorCalldata <- mapM (getCalldataValue solver ctorIface) ctorDecls
  calllocs <- mapM (getLocationValue solver ctorIface Pre) clocs
  environment <- mapM (getEnvironmentValue solver) env
  pure $ Model
    { _mprestate = prestate
    , _mpoststate = poststate
    , _mcalldata = (behvIface, behvCalldata)
    , _mcalllocs = calllocs
    , _menvironment = environment
    , _minitargs = ctorCalldata
    }

-- | Extracts an assignment for the variables in the given constructor
getCtorModel :: Constructor -> SolverInstance -> IO Model
getCtorModel ctor solver = do
  let locs = locsFromConstructor ctor
      (slocs, clocs) = partitionLocs locs
      env = ethEnvFromConstructor ctor
      Interface ifaceName decls = _cinterface ctor
  poststate <- mapM (getLocationValue solver ifaceName Post) slocs
  calldata <- mapM (getCalldataValue solver ifaceName) decls
  calllocs <- mapM (getLocationValue solver ifaceName Pre) clocs
  environment <- mapM (getEnvironmentValue solver) env
  pure $ Model
    { _mprestate = []
    , _mpoststate = poststate
    , _mcalldata = (ifaceName, calldata)
    , _mcalllocs = calllocs
    , _menvironment = environment
    , _minitargs = []
    }

collectArrayExps :: [TypedExp] -> TypedExp
collectArrayExps tl = case tl of
  (TExp styp1 _ ):_ -> TExp newType $ Array nowhere $ map (cmpType styp1) tl
    where
      newType = TArray (length tl) styp1

      cmpType :: TValueType a -> TypedExp -> Exp a
      cmpType styp (TExp styp' e') =
        maybe (error "Internal error: unreachable after typing") (\Refl -> e') $ testEquality styp styp'
  [] -> error "Internal error: cannot type empty array"

-- | Gets a concrete value from the solver for all elements of an array
getArrayExp :: SolverInstance -> TValueType a -> Id -> NonEmpty Int -> [Int] -> IO (TypedExp)
getArrayExp solver typ name (h:|[]) idcs = collectArrayExps <$> typedExps
  where
    typedExps = mapM getArrayElement (map ((++) idcs . singleton)  [0..(h-1)])

    getArrayElement :: [Int] -> IO TypedExp
    getArrayElement idcs' =
      parseModel typ <$> getValue solver (selectIntIdx name $ NonEmpty.fromList idcs')
getArrayExp solver typ name (h:|t) idcs = collectArrayExps <$> typedExps
  where
    typedExps = sequence $
      getArrayExp solver typ name (NonEmpty.fromList t) <$> map ((++) idcs . singleton)  [0..(h-1)]

-- | Gets a concrete value from the solver for the given location
getLocationValue :: SolverInstance -> Id -> When -> Location -> IO (Location, TypedExp)
getLocationValue solver ifaceName whn loc@(Loc (flattenValueType -> (baseType, _)) _ item@(Item vt _)) = do
  output <- case flattenValueType vt of
    (_, Nothing) -> (parseModel baseType) <$> getValue solver name
    (_, Just shape) -> getArrayExp solver baseType name shape []
  -- TODO: handle errors here...
  pure (loc, output)
  where
    name = withInterface ifaceName $
            if isIndexed item
            then select whn item (NonEmpty.fromList $ ixsFromItem item)
            else nameFromItem whn item
--getLocationValue solver ifaceName whn loc@(Loc styp _ item@(Item _ (ContractType _) _)) = do
--  output <- (parseModel styp) <$> getValue solver name
--  -- TODO: handle errors here...
--  pure (loc, output)
--  where
--    name = withInterface ifaceName $
--            if isIndexed item
--            then select whn item (NonEmpty.fromList $ ixsFromItem item)
--            else nameFromItem whn item

-- | Gets a concrete value from the solver for the given calldata argument
getCalldataValue :: SolverInstance -> Id -> Decl -> IO (Decl, TypedExp)
getCalldataValue solver ifaceName decl@(Decl vt _) =
  case flattenArrayAbiType vt of
    Just (fromAbiType' -> ValueType baseType, shape) -> do
      array' <- getArrayExp solver baseType name shape []
      pure (decl, array')
      where
        name = nameFromDecl ifaceName decl
    Nothing ->
      case vt of
        (fromAbiType' -> ValueType tp) -> do
          val <- parseModel tp <$> getValue solver (nameFromDecl ifaceName decl)
          pure (decl, val)

-- | Gets a concrete value from the solver for the given environment variable
getEnvironmentValue :: SolverInstance -> EthEnv -> IO (EthEnv, TypedExp)
getEnvironmentValue solver env = do
  output <- getValue solver (prettyEnv env)
  let val = case lookup env globalEnv of
        Just t -> parseModel t output -- TODO: is this type accurate ?
        _ -> error $ "Internal Error: could not determine a type for" <> show env
  pure (env, val)

-- | Calls `(get-value)` for the given identifier in the given solver instance.
getValue :: SolverInstance -> String -> IO String
getValue solver name = sendCommand solver $ "(get-value (" <> name <> "))"

-- | Parse the result of a call to getValue as the supplied type.
parseModel :: TValueType a -> String -> TypedExp
parseModel = \case
  t@(TInteger _ _) -> TExp t . LitInt  nowhere . read       . parseSMTModel
  TBoolean -> TExp TBoolean . LitBool nowhere . readBool   . parseSMTModel
  TByteStr -> TExp TByteStr . ByLit   nowhere . fromString . parseSMTModel
  TAddress -> TExp TAddress . LitInt   nowhere . read . parseSMTModel
  (TArray _ _) -> error "TODO array parse model"
  (TStruct _) -> error "TODO struct parse model"
  (TContract c) -> error "TODO contract parse model"
  where
    readBool "true" = True
    readBool "false" = False
    readBool s = error ("Could not parse " <> s <> "into a bool")

-- | Extracts a string representation of the value in the output from a call to `(get-value)`
parseSMTModel :: String -> String
parseSMTModel s
  | length capNoPar == 1 = head capNoPar
  | length capPar == 1 = head capPar
  | otherwise = ""
  where
    -- output should be in the form "((reference value))" for positive integers / booleans / strings
    -- or "((reference (value)))" for negative integers.
    -- where reference is either an identifier or a sequence of nested selections
    noPar = "\\`\\(\\([ \\(\\)a-zA-Z0-9_\\+\\*\\=\\<\\>\\.\\-]+ ([ \"a-zA-Z0-9_\\-]+)\\)\\)\\'" :: String
    par = "\\`\\(\\([ \\(\\)a-zA-Z0-9_\\+\\*\\=\\<\\>\\.\\-]+ \\(([ \"a-zA-Z0-9_\\-]+)\\)\\)\\)\\'" :: String

    capNoPar = getCaptures s noPar
    capPar = getCaptures s par

    getCaptures :: String -> String -> [String]
    getCaptures str regex = captures
      where (_, _, _, captures) = str =~ regex :: (String, String, String, [String])


--- ** SMT2 Generation ** ---


mkEqualityAssertion :: Location -> Location -> Exp ABoolean
mkEqualityAssertion l1 l2 = foldr mkAnd (LitBool nowhere True) (zipWith eqIdx ix1 ix2)
  where
    ix1 = ixsFromLocation l1
    ix2 = ixsFromLocation l2

    eqIdx :: TypedExp -> TypedExp -> Exp ABoolean
    -- TODO: check if integer type matters here, maybe not if all equalities are translated the same, hopefully
    eqIdx (TExp (TInteger _ _) e1) (TExp (TInteger _ _) e2) = Eq nowhere (TInteger 256 Signed) e1 e2
    eqIdx (TExp TAddress e1) (TExp TAddress e2) = Eq nowhere (TInteger 256 Signed) e1 e2
    eqIdx _ _ = error "Internal error: Expected Integer index expressions"

    mkAnd r c = And nowhere c r

mkConstantAssertion :: Id -> [Location] -> Location -> SMT2
mkConstantAssertion name updates loc@(Loc _ _ item) = constancy
  where
    currentIds = idsFromLocation loc
    relevantUpdates = filter ((==) currentIds . idsFromLocation) updates

    aliasedAssertions = mkEqualityAssertion loc <$> relevantUpdates
    isConstantAssertion = foldl mkAnd (LitBool nowhere True) aliasedAssertions

    locSMTRep whn = if isIndexed item
      then withInterface name $ select whn item (NonEmpty.fromList $ ixsFromItem item)
      else withInterface name $ nameFromItem whn item

    constancy = case updates of
      [] -> "(assert (= "  <> locSMTRep Pre <> " " <> locSMTRep Post <> "))"
      _  -> "(assert (=> " <> withInterface name (expToSMT2 TBoolean isConstantAssertion)
                           <> " (= " <> locSMTRep Pre <> " " <> locSMTRep Post <> ")))"

    mkAnd r c = And nowhere (Neg nowhere c) r


-- | encodes lack of update for a location as an smt assertion
encodeConstant :: Id -> [Location] -> [Location] -> [SMT2]
encodeConstant name updated locs = fmap (mkConstantAssertion name updated) locs

-- | encodes a storage update rewrite as an smt assertion
encodeUpdate :: Id -> StorageUpdate -> SMT2
encodeUpdate ifaceName (Update typ item expr) =
  let
    postentry  = withInterface ifaceName $ expToSMT2 typ (VarRef nowhere Post SStorage item)
    expression = withInterface ifaceName $ expToSMT2 typ expr
  in "(assert (= " <> postentry <> " " <> expression <> "))"

declareLoc :: Id -> [When] -> Location -> [SMT2]
declareLoc ifaceName times (Loc _ rk item@(Item _ ref)) = (flip declareRef ref) <$> names
  where
    names = case rk of
      SStorage -> flip nameFromSItem item <$> times
      SCalldata -> [nameFromCItem ifaceName item]
    declareRef itemName (CVar _ _ _) = constant itemName (itemType item)
    declareRef itemName (SVar _ _ _) = constant itemName (itemType item)
    declareRef itemName (SArray _ _ _ ixs) = array itemName (length ixs) (itemType item)
    declareRef itemName (SMapping _ _ _ ixs) = mappingArray itemName ixs (itemType item)
    declareRef itemName (SField _ ref' _ _) = declareRef itemName ref'


-- | declares a storage location that is created by the constructor, these
--   locations have no prestate, so we declare a post var only
declareInitialLocation :: Id -> Location -> [SMT2]
declareInitialLocation ifaceName item = declareLoc ifaceName [Post] item

-- | declares a storage location that exists both in the pre state and the post
--   state (i.e. anything except a loc created by a constructor claim)
declareLocation :: Id -> Location -> [SMT2]
declareLocation ifaceName item = declareLoc ifaceName [Pre, Post] item

-- | produces an SMT2 expression declaring the given decl as a symbolic constant
declareArg :: Id -> Decl -> SMT2
declareArg ifaceName d@(Decl atyp@(fromAbiType' -> ValueType typ) _) =
  case flattenArrayAbiType atyp of
    Just (fromAbiType' -> ValueType baseTyp, shape) ->
       array (nameFromDecl ifaceName d) (length shape) baseTyp
    Nothing -> constant (nameFromDecl ifaceName d) typ

-- | produces an SMT2 expression declaring the given EthEnv as a symbolic constant
declareEthEnv :: EthEnv -> SMT2
declareEthEnv env = constant (prettyEnv env) tp
  where tp = fromJust . lookup env $ globalEnv

-- | encodes a typed expression as an smt2 expression
typedExpToSMT2 :: TypedExp -> Ctx SMT2
typedExpToSMT2 (TExp typ e) = expToSMT2 typ e

-- | encodes the given Exp as an smt2 expression
expToSMT2 :: forall (a :: ActType). TValueType a -> Exp a -> Ctx SMT2
expToSMT2 typ expr = case expr of
  -- booleans
  And _ a b -> binop "and" TBoolean TBoolean a b
  Or _ a b -> binop "or" TBoolean TBoolean a b
  Impl _ a b -> binop "=>" TBoolean TBoolean a b
  Neg _ a -> unop "not" TBoolean a
  LT _ a b -> binop "<" (TInteger 256 Unsigned) (TInteger 256 Unsigned) a b
  LEQ _ a b -> binop "<=" (TInteger 256 Unsigned) (TInteger 256 Unsigned) a b
  GEQ _ a b -> binop ">=" (TInteger 256 Unsigned) (TInteger 256 Unsigned) a b
  GT _ a b -> binop ">" (TInteger 256 Unsigned) (TInteger 256 Unsigned) a b
  LitBool _ a -> pure $ if a then "true" else "false"

  -- integers
  Add _ a b -> binop "+" (TInteger 256 Unsigned) (TInteger 256 Unsigned) a b
  Sub _ a b -> binop "-" (TInteger 256 Unsigned) (TInteger 256 Unsigned) a b
  Mul _ a b -> binop "*" (TInteger 256 Unsigned) (TInteger 256 Unsigned) a b
  Div _ a b -> binop "div" (TInteger 256 Unsigned) (TInteger 256 Unsigned) a b
  Mod _ a b -> binop "mod" (TInteger 256 Unsigned) (TInteger 256 Unsigned) a b
  Exp _ a b -> expToSMT2 typ $ simplifyExponentiation a b
  LitInt _ a -> pure $ if a >= 0
                      then show a
                      else "(- " <> (show . negate $ a) <> ")" -- cvc4 does not accept negative integer literals
  IntEnv _ a -> pure $ prettyEnv a

  -- bounds
  IntMin p a -> expToSMT2 typ . LitInt p $ intmin a
  IntMax _ a -> pure . show $ intmax a
  UIntMin _ a -> pure . show $ uintmin a
  UIntMax _ a -> pure . show $ uintmax a
  InRange _ t e -> expToSMT2 typ (bound t e)

  -- bytestrings
  Cat _ a b -> binop "str.++" TByteStr TByteStr a b
  Slice p a start end -> triop "str.substr" TByteStr (TInteger 256 Unsigned) (TInteger 256 Unsigned) a start (Sub p end start)
  ByStr _ a -> pure a
  ByLit _ a -> pure $ show a
  ByEnv _ a -> pure $ prettyEnv a

  Array _ l -> case typ of
    (TArray _ typ') ->
      [ foldr (\s1 s2 -> "(store " <> s2 <> " " <> show (fst s1 :: Integer) <> " " <> snd s1 <> ")" )
            (defaultConst typ) $ zip [0..] l' | l' <- mapM (expToSMT2 typ') l ]
        where
          defaultConst :: TValueType a -> SMT2
          defaultConst t@(TArray _ t') = "((as const " <> (vType t) <> ") " <> (defaultConst t') <> ")"
          defaultConst (TInteger _ _) = "0"
          defaultConst TBoolean = "false"
          defaultConst TByteStr = error "TODO"
          defaultConst TAddress = error "TODO"
          defaultConst (TContract _) = error "TODO"
          defaultConst (TStruct _) = error "TODO"

  -- contracts
  Create _ _ _ -> pure "0" -- TODO just a dummy address for now

  -- polymorphic
  --  For array comparisons, expands both arrays to their elements and compares elementwise,
  --  as SMT's default array equality requires equality for all possible Int values,
  --  not only for indices within defined bounds. Same for Neq.
  Eq p s@(TArray _ _) a b -> expToSMT2 TBoolean expanded
    where
      a' = expandArrayExpr s a
      b' = expandArrayExpr s b
      s' = fst $ flattenValueType s
      eqs = (uncurry $ Eq p s') <$> zip a' b'
      expanded = foldr (And nowhere) (LitBool nowhere True) eqs
  Eq _ s a b -> binop "=" s s a b

  NEq p s@(TArray _ _) a b -> expToSMT2 TBoolean expanded
    where
      a' = expandArrayExpr s a
      b' = expandArrayExpr s b
      s' = fst $ flattenValueType s
      eqs = (uncurry $ NEq p s') <$> zip a' b'
      expanded = foldr (Or nowhere) (LitBool nowhere False) eqs
  NEq p s a b -> unop "not" TBoolean (Eq p s a b)

  ITE _ a b c -> triop "ite" TBoolean typ typ a b c
  VarRef _ whn _ item -> entry whn item
  where
    unop :: String -> TValueType a -> Exp a -> Ctx SMT2
    unop op t a = [ "(" <> op <> " " <> a' <> ")" | a' <- expToSMT2 t a]

    binop :: String -> TValueType a -> TValueType b -> Exp a -> Exp b -> Ctx SMT2
    binop op t1 t2 a b = [ "(" <> op <> " " <> a' <> " " <> b' <> ")"
                       | a' <- expToSMT2 t1 a, b' <- expToSMT2 t2 b]

    triop :: String -> TValueType a -> TValueType b -> TValueType c -> Exp a -> Exp b -> Exp c -> Ctx SMT2
    triop op t1 t2 t3 a b c = [ "(" <> op <> " " <> a' <> " " <> b' <> " " <> c' <> ")"
                         | a' <- expToSMT2 t1 a, b' <- expToSMT2 t2 b, c' <- expToSMT2 t3 c]

    entry :: When -> TItem a k -> Ctx SMT2
    entry whn item = case ixsFromItem item of
      []       -> nameFromItem whn item
      (ix:ixs) -> do
        select whn item (ix :| ixs)


-- | SMT2 has no support for exponentiation, but we can do some preprocessing
--   if the RHS is concrete to provide some limited support for exponentiation
simplifyExponentiation :: Exp AInteger -> Exp AInteger -> Exp AInteger
simplifyExponentiation a b = fromMaybe (error "Internal Error: no support for symbolic exponents in SMT lib")
                           $ [LitInt nowhere $ a' ^ b'                         | a' <- eval a, b' <- evalb]
                         <|> [foldr (Mul nowhere) (LitInt nowhere 1) (genericReplicate b' a) | b' <- evalb]
  where
    evalb = eval b -- TODO is this actually necessary to prevent double evaluation?

-- | declare a constant in smt2
constant :: Id -> TValueType a -> SMT2
constant name tp = "(declare-const " <> name <> " " <> vType tp <> ")"

-- | encode the given boolean expression as an assertion in smt2
mkAssert :: Id -> Exp ABoolean -> SMT2
mkAssert c e = "(assert " <> withInterface c (expToSMT2 TBoolean e) <> ")"

-- | declare a (potentially nested) array in smt2
array :: Id -> Int -> TValueType a -> SMT2
array name argNum ret = "(declare-const " <> name <> " " <> valueDecl argNum <> ")"
  where
    valueDecl n | n <= 0 = vType ret
    valueDecl n = "(Array " <> sType AInteger <> " " <> valueDecl (n-1) <> ")"

-- | declare a (potentially nested) array representing a mapping in smt2
mappingArray :: Id -> [TypedExp] -> TValueType a -> SMT2
mappingArray name args ret = "(declare-const " <> name <> valueDecl args <> ")"
  where
    valueDecl [] = vType ret
    valueDecl (h : t) = "(Array " <> sType' h <> " " <> valueDecl t <> ")"

-- | encode an array lookup with Integer indices in smt2
selectIntIdx :: String -> NonEmpty Int -> SMT2
selectIntIdx name (hd :| tl) = do
  foldl (\smt ix -> "(select " <> smt <> " " <> show ix <> ")" ) ("(select " <> name <> " " <> show hd <> ")") tl

-- | encode an indexed lookup in smt2
select :: When -> TItem a k -> NonEmpty TypedExp -> Ctx SMT2
select whn item (hd :| tl) = do
  inner <- [ "(select " <> name <> " " <> hd' <> ")" | hd' <- typedExpToSMT2 hd, name <- nameFromItem whn item]
  foldM (\smt ix -> [ "(select " <> smt <> " " <> ix' <> ")" | ix' <- typedExpToSMT2 ix]) inner tl

-- | act -> smt2 type translation
sType :: ActType -> SMT2
sType AInteger = "Int"
sType ABoolean = "Bool"
sType AByteStr = "String"
sType AStruct = error "TODO"
sType AContract = error "TODO"
sType (AArray a) = "(Array " <> sType AInteger <> " " <> sType a <> ")"

vType :: TValueType a -> SMT2
vType (TInteger _ _) = "Int"
vType TBoolean = "Bool"
vType TByteStr = "String"
vType TAddress = "Int"
vType (TContract _) = "Int"
vType (TStruct _) = error "TODO"
vType (TArray _ a) = "(Array " <> sType AInteger <> " " <> vType a <> ")"


-- | act -> smt2 type translation
sType' :: TypedExp -> SMT2
sType' (TExp t _) = vType t

--- ** Variable Names ** ---

-- Construct the smt2 variable name for a given storage item
nameFromSItem :: When -> TItem a Storage -> Id
nameFromSItem whn (Item _ ref) = nameFromSRef whn ref

nameFromSRef :: When -> Ref Storage -> Id
nameFromSRef whn (SVar _ c name) = c @@ name @@ show whn
nameFromSRef whn (SArray _ e _ _) = nameFromSRef whn e
nameFromSRef whn (SMapping _ e _ _) = nameFromSRef whn e
nameFromSRef whn (SField _ ref c x) = nameFromSRef whn ref @@ c @@ x

nameFromCItem :: Id -> TItem a Calldata -> Id
nameFromCItem behvName (Item _ ref) = nameFromCRef behvName ref

nameFromCRef :: Id -> Ref Calldata -> Id
nameFromCRef behvName (CVar _ _ name) = behvName @@ name
nameFromCRef behvName (SArray _ e _ _) = nameFromCRef behvName e
nameFromCRef behvName (SMapping _ e _ _) = nameFromCRef behvName e
nameFromCRef behvName (SField _ ref c x) = nameFromCRef behvName ref @@ c @@ x

nameFromItem ::When ->  TItem k a -> Ctx Id
nameFromItem whn (Item _ ref) = nameFromRef whn ref

nameFromRef :: When -> Ref k -> Ctx Id
nameFromRef _ (CVar _ _ name) = nameFromVarId name
nameFromRef whn (SVar _ c name) = pure $ c @@ name @@ show whn
nameFromRef whn (SArray _ e _ _) = nameFromRef whn e
nameFromRef whn (SMapping _ e _ _) = nameFromRef whn e
nameFromRef whn (SField _ ref c x) = do
  name <- nameFromRef whn ref
  pure $ name @@ c @@ x


-- Construct the smt2 variable name for a given decl
nameFromDecl :: Id -> Decl -> Id
nameFromDecl ifaceName (Decl _ name) = ifaceName @@ name

-- Construct the smt2 variable name for a given act variable
nameFromVarId :: Id -> Ctx Id
nameFromVarId name = [behvName @@ name | behvName <- ask]

(@@) :: String -> String -> String
x @@ y = x <> "_" <> y

--- ** Util ** ---

-- | The target expression of a query.
target :: Query -> Exp ABoolean
target (Postcondition _ e _)         = e
target (Inv (Invariant _ _ _ e) _ _) = invExp e

getQueryContract :: Query -> Id
getQueryContract (Postcondition (Ctor ctor) _ _) = _cname ctor
getQueryContract (Postcondition (Behv behv) _ _) = _contract behv
getQueryContract (Inv (Invariant c _ _ _) _ _) = c

isFail :: SMTResult -> Bool
isFail Unsat = False
isFail _ = True

isPass :: SMTResult -> Bool
isPass = not . isFail

getBehvName :: Query -> DocAnsi
getBehvName (Postcondition (Ctor _) _ _) = (pretty "the") <+> (bold . pretty $ "constructor")
getBehvName (Postcondition (Behv behv) _ _) = (pretty "behaviour") <+> (bold . pretty $ _name behv)
getBehvName (Inv {}) = error "Internal Error: invariant queries do not have an associated behaviour"

identifier :: Query -> DocAnsi
identifier q@(Inv (Invariant _ _ _ e) _ _)    = (bold . pretty . prettyInvPred $ e) <+> pretty "of" <+> (bold . pretty . getQueryContract $ q)
identifier q@Postcondition {} = (bold . pretty . prettyExp . target $ q) <+> pretty "in" <+> getBehvName q <+> pretty "of" <+> (bold . pretty . getQueryContract $ q)

getSMT :: Query -> DocAnsi
getSMT (Postcondition _ _ smt) = prettyAnsi smt
getSMT (Inv _ (_, csmt) behvs) = pretty "; constructor" <$$> sep' <$$> line <> prettyAnsi csmt <$$> vsep (fmap formatBehv behvs)
  where
    formatBehv (b, smt) = line <> pretty "; behaviour: " <> (pretty . _name $ b) <$$> sep' <$$> line <> prettyAnsi smt
    sep' = pretty "; -------------------------------"

ifExists :: Foldable t => t a -> DocAnsi -> DocAnsi
ifExists a b = if null a then emptyDoc else b
