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
  --mkPostconditionQueries,
  --mkPostconditionQueriesBehv,
  --mkInvariantQueries,
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
  declareTRef,
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
import qualified Data.Map as M
import Data.List
import GHC.IO.Handle (Handle, hGetLine, hPutStr, hFlush)
import Data.ByteString.UTF8 (fromString)

import Act.Syntax
import Act.Syntax.TypedExplicit hiding (array)

import Act.Print

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
  { _mprestate :: [(TypedRef, TypedExp)]
  , _mpoststate :: [(TypedRef, TypedExp)]
  , _mcalldata :: (String, [(Arg, TypedExp)])
  , _mcalllocs :: [(TypedRef, TypedExp)]
  , _menvironment :: [(EthEnv, TypedExp)]
  -- invariants always have access to the constructor context
  , _minitargs :: [(Arg, TypedExp)]
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
      formatCalldata (Arg _ name, val) = pretty $ name <> " = " <> prettyTypedExp val
      formatEnvironment (env, val) = pretty $ prettyEnv env <> " = " <> prettyTypedExp val
      formatStorage (loc, val) = pretty $ prettyTypedRef loc <> " = " <> prettyTypedExp val


data SolverInstance = SolverInstance
  { _type :: Solver
  , _stdin :: Handle
  , _stdout :: Handle
  , _stderr :: Handle
  , _process :: ProcessHandle
  }


--- ** Analysis Passes ** ---

-- | Produces an SMT expression in a format that services most SMT passes.
-- Zoe: Can we merge preconds and extraconds?
mkDefaultSMT :: [TypedRef] -> [EthEnv] -> Id -> [Arg] -> [Exp ABoolean] -> [Exp ABoolean] -> Exp ABoolean -> SMTExp
mkDefaultSMT refs envs ifaceName args preconds extraconds = mksmt
  where
    -- Declare calldata arguments and locations, and environmental variables
    storage = nub (declareTRef <$> refs)
    ifaceArgs = nub $ (declareArg ifaceName <$> args) \\ storage
    env = nub $ declareEthEnv <$> envs

    -- Constraints
    pres = mkAssert ifaceName <$> preconds <> extraconds

    mksmt e = SMTExp
      { _storage = storage
      , _calldata = ifaceArgs
      , _environment = env
      , _assertions = [mkAssert ifaceName e] <> pres
      }

{-
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
mkPostconditionQueriesBehv behv@(Behaviour _ _ (Interface ifaceName decls) _ preconds caseconds postconds) =
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

-}
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
  -- traceM $ "Entailment SMT Query:\n" <> renderString (prettyAnsi smt)
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
    -- traceM cmd
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
--      (slocs, clocs) = partitionLocs locs
      env = ethEnvFromBehaviour behv
      name = _name behv
      Interface _ decls = _interface behv
  prestate <- mapM (getLocationValue solver name Pre) locs
  poststate <- mapM (getLocationValue solver name Post) locs
  calldata <- mapM (getCalldataValue solver name) decls
  calllocs <- mapM (getLocationValue solver name Pre) locs -- Pre will be ignored in all calllocs
  environment <- mapM (getEnvironmentValue solver) env
  pure $ Model
    { _mprestate = prestate
    , _mpoststate = poststate
    , _mcalldata = (name, calldata)
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
      --(slocs, clocs) = partitionLocs locs
      env = nub $ ethEnvFromBehaviour behv <> ethEnvFromExp (invExp predicate)
      bname = _name behv
      cname = _cname ctor
      Interface _ behvDecls = _interface behv
      Interface _ ctorDecls = _cinterface ctor
  -- TODO: v ugly to ignore the ifaceName here, but it's safe...
  prestate <- mapM (getLocationValue solver "" Pre) locs
  poststate <- mapM (getLocationValue solver "" Post) locs
  behvCalldata <- mapM (getCalldataValue solver bname) behvDecls
  ctorCalldata <- mapM (getCalldataValue solver cname) ctorDecls
  calllocs <- mapM (getLocationValue solver cname Pre) locs
  environment <- mapM (getEnvironmentValue solver) env
  pure $ Model
    { _mprestate = prestate
    , _mpoststate = poststate
    , _mcalldata = (bname, behvCalldata)
    , _mcalllocs = calllocs
    , _menvironment = environment
    , _minitargs = ctorCalldata
    }

-- | Extracts an assignment for the variables in the given constructor
getCtorModel :: Constructor -> SolverInstance -> IO Model
getCtorModel ctor solver = do
  let locs = locsFromConstructor ctor
      --(slocs, clocs) = partitionLocs locs
      env = ethEnvFromConstructor ctor
      cname = _cname ctor
      Interface _ decls = _cinterface ctor
  poststate <- mapM (getLocationValue solver cname Post) locs
  calldata <- mapM (getCalldataValue solver cname) decls
  calllocs <- mapM (getLocationValue solver cname Pre) locs
  environment <- mapM (getEnvironmentValue solver) env
  pure $ Model
    { _mprestate = []
    , _mpoststate = poststate
    , _mcalldata = (cname, calldata)
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
getLocationValue :: SolverInstance -> Id -> When -> TypedRef -> IO (TypedRef, TypedExp)
getLocationValue solver ifaceName _ tref@(TRef vt@(flattenValueType -> (baseType, _)) _ ref) = do
  output <- case flattenValueType vt of
    (_, Nothing) -> (parseModel baseType) <$> getValue solver name
    (_, Just shape) -> getArrayExp solver baseType name shape []
  -- TODO: handle errors here...
  pure (tref, output)
  where
    name = withInterface ifaceName $
            if isIndexed tref
            then select ref (NonEmpty.fromList $ ixsFromTRef tref)
            else pure $ nameFromTRef tref
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
getCalldataValue :: SolverInstance -> Id -> Arg -> IO (Arg, TypedExp)
getCalldataValue solver ifaceName decl@(Arg (argToAbiType -> vt) _) =
  case flattenArrayAbiType vt of
    Just (fromAbiType -> ValueType baseType, shape) -> do
      array' <- getArrayExp solver baseType name shape []
      pure (decl, array')
      where
        name = nameFromArg ifaceName decl
    Nothing ->
      case vt of
        (fromAbiType -> ValueType tp) -> do
          val <- parseModel tp <$> getValue solver (nameFromArg ifaceName decl)
          pure (decl, val)

-- | Gets a concrete value from the solver for the given environment variable
getEnvironmentValue :: SolverInstance -> EthEnv -> IO (EthEnv, TypedExp)
getEnvironmentValue solver env = do
  output <- getValue solver (prettyEnv env)
  let val = parseModel (ethEnv env) output -- TODO: is this type accurate ?
  pure (env, val)

-- | Calls `(get-value)` for the given identifier in the given solver instance.
getValue :: SolverInstance -> String -> IO String
getValue solver name = sendCommand solver $ "(get-value (" <> name <> "))"

-- | Parse the result of a call to getValue as the supplied type.
parseModel :: TValueType a -> String -> TypedExp
parseModel = \case
  t@(TInteger _ _) -> TExp t . LitInt  nowhere . read       . parseSMTModel
  t@TUnboundedInt -> TExp t . LitInt  nowhere . read       . parseSMTModel
  TBoolean -> TExp TBoolean . LitBool nowhere . readBool   . parseSMTModel
  TByteStr -> TExp TByteStr . ByLit   nowhere . fromString . parseSMTModel
  TAddress -> TExp TAddress . LitInt   nowhere . read . parseSMTModel
  (TArray _ _) -> error "TODO array parse model"
  (TMapping _ _) -> error "TODO array parse model"
  (TStruct _) -> error "TODO struct parse model"
  (TContract _) -> error "TODO contract parse model"
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

stateName :: Id -> SMT2
stateName cid = cid <> "_state"

declareStateDatatype :: Id -> M.Map Id (ValueType, Integer) -> SMT2
declareStateDatatype contract storageUnsorted =
  "(declare-datatype " <> stateName contract <> " ((" <> stateName contract <> " " <>  fields <> ")))"
  where
    storage = sortOn (snd . snd) $ M.toList storageUnsorted
    fields = intercalate " " $ fieldDecl <$> storage

    fieldDecl :: (Id, (ValueType, Integer)) -> SMT2
    fieldDecl (var,(vt,_)) = "(" <> var <> " " <> valueTypeToSMT2 vt <> ")"

valueTypeToSMT2 :: ValueType -> SMT2
valueTypeToSMT2 (ValueType vt) = tValueTypeToSMT2 vt

tValueTypeToSMT2 :: TValueType a -> SMT2
tValueTypeToSMT2 (TInteger _ _) = "Int"
tValueTypeToSMT2 TUnboundedInt = "Int"
tValueTypeToSMT2 TAddress = "Int"
tValueTypeToSMT2 TBoolean = "Bool"
tValueTypeToSMT2 TByteStr = "String"
tValueTypeToSMT2 (TContract cid) = cid
tValueTypeToSMT2 (TMapping key t) =
  "(Array " <> valueTypeToSMT2 key <> " " <> valueTypeToSMT2 t <> ")"
tValueTypeToSMT2 (TArray _ t) =
  "(Array Int " <> tValueTypeToSMT2 t <> ")"
tValueTypeToSMT2 (TStruct _) = error "TODO struct not supported"

mkEqualityAssertion :: TypedRef -> TypedRef -> Exp ABoolean
mkEqualityAssertion l1 l2 = foldr mkAnd (LitBool nowhere True) (zipWith eqIdx ix1 ix2)
  where
    ix1 = ixsFromTRef l1
    ix2 = ixsFromTRef l2

    eqIdx :: TypedExp -> TypedExp -> Exp ABoolean
    -- TODO: check if integer type matters here, maybe not if all equalities are translated the same, hopefully
    eqIdx (TExp (TInteger _ _) e1) (TExp (TInteger _ _) e2) = Eq nowhere (TInteger 256 Signed) e1 e2
    eqIdx (TExp TAddress e1) (TExp TAddress e2) = Eq nowhere (TInteger 256 Signed) e1 e2
    eqIdx _ _ = error "Internal error: Expected Integer index expressions"

    mkAnd r c = And nowhere c r

mkConstantAssertion :: Id -> [TypedRef] -> TypedRef -> SMT2
mkConstantAssertion name updates tref@(TRef _ _ ref) = constancy
  where
    currentIds = idsFromTRef tref
    relevantUpdates = filter ((==) currentIds . idsFromTRef) updates

    aliasedAssertions = mkEqualityAssertion tref <$> relevantUpdates
    isConstantAssertion = foldl mkAnd (LitBool nowhere True) aliasedAssertions

    locSMTRep whn = if isIndexed tref
      then withInterface name $ select ref (NonEmpty.fromList $ ixsFromRef ref)
      else nameFromTRef tref

    constancy = case updates of
      [] -> "(assert (= "  <> locSMTRep Pre <> " " <> locSMTRep Post <> "))"
      _  -> "(assert (=> " <> withInterface name (expToSMT2 SBoolean isConstantAssertion)
                           <> " (= " <> locSMTRep Pre <> " " <> locSMTRep Post <> ")))"

    mkAnd r c = And nowhere (Neg nowhere c) r


-- | encodes lack of update for a location as an smt assertion
encodeConstant :: Id -> [TypedRef] -> [TypedRef] -> [SMT2]
encodeConstant name updated locs = fmap (mkConstantAssertion name updated) locs


-- | encodes a storage update rewrite as an smt assertion
encodeUpdate :: Id -> StorageUpdate -> SMT2
encodeUpdate ifaceName (Update typ item expr) =
  let
    postentry  = withInterface ifaceName $ expToSMT2 (toSType typ) (VarRef nowhere typ (refToRHS item))
    expression = withInterface ifaceName $ expToSMT2 (toSType typ) expr
  in "(assert (= " <> postentry <> " " <> expression <> "))"

declareTRef :: TypedRef -> SMT2
declareTRef (TRef typ _ ref) = declareRef typ name ref
  where
    name = nameFromRef ref -- case rk of
      --SRHS -> flip nameFromItem item <$> times -- TODO: this is most definitely wrong
      --SLHS -> [nameFromRef ref]
    -- This is kind of dumb, recursion over the reference is used to reconstruct the type.
    -- In the future we should probably make declarations from StorageTyping.
    declareRef :: TValueType a -> Id -> Ref k -> SMT2
    declareRef t@VType n (RMapIdx _ (TRef _ _ r) (TExp et _)) = declareRef (TMapping (ValueType et) (ValueType t)) n r
    declareRef t n (RArrIdx _ r _ b) = declareRef (TArray b t) n r
    declareRef t n (CVar _ _ _) = constant n t
    declareRef t n (SVar _ _ _ _) = constant n t
    declareRef t n (RField _ _ _ _) = constant n t

-- | produces an SMT2 expression declaring the given decl as a symbolic constant
declareArg :: Id -> Arg -> SMT2
declareArg ifaceName d@(Arg atyp@((fromAbiType . argToAbiType) -> ValueType typ) _) =
  case flattenArrayAbiType (argToAbiType atyp) of
    Just (fromAbiType -> ValueType baseTyp, shape) ->
       array (nameFromArg ifaceName d) (length shape) baseTyp
    Nothing -> constant (nameFromArg ifaceName d) typ

-- | produces an SMT2 expression declaring the given EthEnv as a symbolic constant
declareEthEnv :: EthEnv -> SMT2
declareEthEnv env = constant (prettyEnv env) tp
  where tp = ethEnv env

-- | encodes a typed expression as an smt2 expression
typedExpToSMT2 :: TypedExp -> Ctx SMT2
typedExpToSMT2 (TExp typ e) = expToSMT2 (toSType typ) e

-- | encodes the given Exp as an smt2 expression
expToSMT2 :: forall (a :: ActType). SType a -> Exp a -> Ctx SMT2
expToSMT2 typ expr = case expr of
  -- calls to create can never return the same result
  -- temproary workaround for lack of contract creation in SMT encoding
  (Eq _ _ (Create _ _ _ _) _) -> pure "false"
  (Eq _ _ _ (Create _ _ _ _)) -> pure "false"
  (NEq _ _ (Create _ _ _ _) _) -> pure "true"
  (NEq _ _ _ (Create _ _ _ _)) -> pure "true"
  (InRange _ TAddress (Address _ _ (Create _ _ _ _))) -> pure "true"
  -- booleans
  And _ a b -> binop "and" SBoolean SBoolean a b
  Or _ a b -> binop "or" SBoolean SBoolean a b
  Impl _ a b -> binop "=>" SBoolean SBoolean a b
  Neg _ a -> unop "not" SBoolean a
  LT _ a b -> binop "<" SInteger SInteger a b
  LEQ _ a b -> binop "<=" SInteger SInteger a b
  GEQ _ a b -> binop ">=" SInteger SInteger a b
  GT _ a b -> binop ">" SInteger SInteger a b
  LitBool _ a -> pure $ if a then "true" else "false"

  -- integers
  Add _ a b -> binop "+" SInteger SInteger a b
  Sub _ a b -> binop "-" SInteger SInteger a b
  Mul _ a b -> binop "*" SInteger SInteger a b
  Div _ a b -> binop "div" SInteger SInteger a b
  Mod _ a b -> binop "mod" SInteger SInteger a b
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
  InRange _ t e -> expToSMT2 typ (And nowhere (LEQ nowhere (lowerBound t) e) $ LEQ nowhere e (upperBound t))

  -- bytestrings
  Cat _ a b -> binop "str.++" SByteStr SByteStr a b
  Slice p a start end -> triop "str.substr" SByteStr SInteger SInteger a start (Sub p end start)
  ByStr _ a -> pure a
  ByLit _ a -> pure $ show a
  ByEnv _ a -> pure $ prettyEnv a

  Array _ l -> case typ of
    (SSArray typ') ->
      [ foldr (\s1 s2 -> "(store " <> s2 <> " " <> show (fst s1 :: Integer) <> " " <> snd s1 <> ")" )
            (defaultConst typ) $ zip [0..] l' | l' <- mapM (expToSMT2 typ') l ]
        where
          defaultConst :: SType a -> SMT2
          defaultConst t@(SSArray t') = "((as const " <> (sType t) <> ") " <> (defaultConst t') <> ")"
          defaultConst SInteger = "0"
          defaultConst SBoolean = "false"
          defaultConst SByteStr = error "TODO"
          defaultConst SContract = error "TODO"
          defaultConst SStruct = error "TODO"

  -- contracts
  Create _ _ _ _ -> error "Internal Error: unexpected create call in the SMT expression"
  -- polymorphic
  --  For array comparisons, expands both arrays to their elements and compares elementwise,
  --  as SMT's default array equality requires equality for all possible Int values,
  --  not only for indices within defined bounds. Same for Neq.
  Eq p s@(TArray _ _) a b -> expToSMT2 SBoolean expanded
    where
      a' = expandArrayExpr s a
      b' = expandArrayExpr s b
      s' = fst $ flattenValueType s
      eqs = (uncurry $ Eq p s') <$> zip a' b'
      expanded = foldr (And nowhere) (LitBool nowhere True) eqs
  Eq _ s a b -> binop "=" (toSType s) (toSType s) a b

  NEq p s@(TArray _ _) a b -> expToSMT2 SBoolean expanded
    where
      a' = expandArrayExpr s a
      b' = expandArrayExpr s b
      s' = fst $ flattenValueType s
      eqs = (uncurry $ NEq p s') <$> zip a' b'
      expanded = foldr (Or nowhere) (LitBool nowhere False) eqs
  NEq p s a b -> unop "not" SBoolean (Eq p s a b)

  ITE _ a b c -> triop "ite" SBoolean typ typ a b c
  VarRef _ _ item -> entry item
  Address _ _ e -> expToSMT2 SContract e -- TODO: get contract, maybe?

  Mapping _ _ _ _ -> expToSMT2 SContract undefined -- TODO
  MappingUpd _ _ _ _ _ -> expToSMT2 SContract undefined
  where
    unop :: String -> SType a -> Exp a -> Ctx SMT2
    unop op t a = [ "(" <> op <> " " <> a' <> ")" | a' <- expToSMT2 t a]

    binop :: String -> SType a -> SType b -> Exp a -> Exp b -> Ctx SMT2
    binop op t1 t2 a b = [ "(" <> op <> " " <> a' <> " " <> b' <> ")"
                       | a' <- expToSMT2 t1 a, b' <- expToSMT2 t2 b]

    triop :: String -> SType a -> SType b -> SType c -> Exp a -> Exp b -> Exp c -> Ctx SMT2
    triop op t1 t2 t3 a b c = [ "(" <> op <> " " <> a' <> " " <> b' <> " " <> c' <> ")"
                         | a' <- expToSMT2 t1 a, b' <- expToSMT2 t2 b, c' <- expToSMT2 t3 c]

    entry :: Ref k -> Ctx SMT2
    entry item = case ixsFromRef item of
      []       -> pure $ nameFromRef item
      (ix:ixs) -> do
        select item (ix :| ixs)


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
mkAssert c e = "(assert " <> withInterface c (expToSMT2 SBoolean e) <> ")"

-- | declare a (potentially nested) array in smt2
array :: Id -> Int -> TValueType a -> SMT2
array name argNum ret = "(declare-const " <> name <> " " <> valueDecl argNum <> ")"
  where
    valueDecl n | n <= 0 = vType ret
    valueDecl n = "(Array " <> aType AInteger <> " " <> valueDecl (n-1) <> ")"

-- | declare a (potentially nested) array representing a mapping in smt2
mappingArray :: Id -> [ValueType] -> TValueType a -> SMT2
mappingArray name args ret = "(declare-const " <> name <> valueDecl args <> ")"
  where
    valueDecl :: [ValueType] -> SMT2
    valueDecl [] = vType ret
    valueDecl ((ValueType h) : t) = "(Array " <> vType h <> " " <> valueDecl t <> ")"

-- | encode an array lookup with Integer indices in smt2
selectIntIdx :: String -> NonEmpty Int -> SMT2
selectIntIdx name (hd :| tl) = do
  foldl (\smt ix -> "(select " <> smt <> " " <> show ix <> ")" ) ("(select " <> name <> " " <> show hd <> ")") tl

-- | encode an indexed lookup in smt2
select :: Ref k -> NonEmpty TypedExp -> Ctx SMT2
select ref (hd :| tl) = do
  let name = nameFromRef ref
  inner <- [ "(select " <> name <> " " <> hd' <> ")" | hd' <- typedExpToSMT2 hd ] --name <- nameFromRef ref]
  foldM (\smt ix -> [ "(select " <> smt <> " " <> ix' <> ")" | ix' <- typedExpToSMT2 ix]) inner tl

-- | act -> smt2 type translation
aType :: ActType -> SMT2
aType AInteger = "Int"
aType ABoolean = "Bool"
aType AByteStr = "String"
aType AStruct = error "TODO"
aType AMapping = error "TODO"
aType AContract = error "TODO"
aType (AArray a) = "(Array " <> aType AInteger <> " " <> aType a <> ")"

sType :: SType a -> SMT2
sType SInteger = "Int"
sType SBoolean = "Bool"
sType SByteStr = "String"
sType SStruct = error "TODO"
sType SMapping = error "TODO"
sType SContract = error "TODO"
sType (SSArray a) = "(Array " <> aType AInteger <> " " <> sType a <> ")"

vType :: TValueType a -> SMT2
vType (TInteger _ _) = "Int"
vType TUnboundedInt = "Int"
vType TBoolean = "Bool"
vType TByteStr = "String"
vType TAddress = "Int"
vType (TContract _) = "Int"
vType (TStruct _) = error "TODO"
vType (TArray _ a) = "(Array " <> aType AInteger <> " " <> vType a <> ")"
vType (TMapping (ValueType k) (ValueType a)) = "(Array " <> vType k <> " " <> vType a <> ")"


-- | act -> smt2 type translation
sType' :: TypedExp -> SMT2
sType' (TExp t _) = vType t

--- ** Variable Names ** ---

-- Construct the smt2 variable name for a given storage item
--nameFromSItem :: When -> TypedRef -> Id
--nameFromSItem whn (TRef _ _ ref) = nameFromSRef whn ref
--
--nameFromSRef :: When -> Ref Storage -> Id
--nameFromSRef whn (SVar _ c name) = c @@ name @@ show whn
--nameFromSRef whn (SArray _ e _ _) = nameFromSRef whn e
--nameFromSRef whn (SMapping _ e _ _) = nameFromSRef whn e
--nameFromSRef whn (SField _ ref c x) = nameFromSRef whn ref @@ c @@ x
--
--nameFromCItem :: Id -> TItem a Calldata -> Id
--nameFromCItem behvName (Item _ ref) = nameFromCRef behvName ref
--
--nameFromCRef :: Id -> Ref Calldata -> Id
--nameFromCRef behvName (CVar _ _ name) = behvName @@ name
--nameFromCRef behvName (SArray _ e _ _) = nameFromCRef behvName e
--nameFromCRef behvName (SMapping _ e _ _) = nameFromCRef behvName e
--nameFromCRef behvName (SField _ ref c x) = nameFromCRef behvName ref @@ c @@ x

nameFromTRef :: TypedRef -> Id
nameFromTRef (TRef _ _ ref) = nameFromRef ref

nameFromRef :: Ref k -> Id
nameFromRef (CVar _ _ name) = nameFromVarId name
nameFromRef (SVar _ whn c name) = c @@ name @@ show whn
nameFromRef (RArrIdx _ e _ _) = nameFromRef e
nameFromRef (RMapIdx _ (TRef _ _ e) _) = nameFromRef e
nameFromRef (RField _ ref c x) = (nameFromRef ref) @@ c @@ x


-- Construct the smt2 variable name for a given decl
nameFromArg :: Id -> Arg -> Id
--nameFromArg ifaceName (Arg _ name) = ifaceName @@ name
nameFromArg _ (Arg _ name) = "arg" @@ name

-- Construct the smt2 variable name for a given act variable
nameFromVarId :: Id -> Id
nameFromVarId name = "arg" @@ name --[behvName @@ name | behvName <- ask]

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
