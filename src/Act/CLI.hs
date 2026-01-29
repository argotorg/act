{-# LANGUAGE DeriveGeneric  #-}
{-# Language DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# Language TypeOperators #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TupleSections #-}

module Act.CLI (main, compile, proceed, prettyErrs) where

import Data.Aeson hiding (Bool, Number, json, Success)
import Data.Aeson.Types hiding (Success, parse)
import GHC.Generics
import System.Exit ( exitFailure )
import System.IO (hPutStrLn, stderr)
import System.Process
import System.FilePath
import Data.Text (unpack)
import Data.Text.Encoding (encodeUtf8)
import Data.List
import Data.Tuple.Extra (firstM)
import Data.Validation
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
import qualified Data.Text as Text
import qualified Data.Text.IO as TIO
import Prettyprinter hiding (annotate, line')
import GHC.Conc
import GHC.Natural
import Options.Generic

import qualified Data.ByteString.Lazy.Char8 as B
import qualified Data.ByteString as BS
import qualified Data.ByteString.Base16 as BS16
import Data.ByteString (ByteString)

import Control.Monad
import Control.Lens.Getter

import Act.Error
import Act.Lex (lexer, AlexPosn(..))
import Act.Parse
import Act.Syntax.TypedExplicit hiding (_Array)
import qualified Act.Syntax.TypedImplicit as TypedImplicit
import Act.Syntax.Timing
import Act.Bounds
import Act.SMT as SMT
import Act.Type hiding (Env)
import Act.Coq hiding (indent, (<+>))
import Act.HEVM
import Act.HEVM_utils
import Act.Consistency
import Act.Print
import Act.Entailment
import Act.Overflow

--import Act.Decompile

import qualified EVM.Solvers as Solvers
import EVM.Solidity
import EVM.Effects
import Control.Arrow (Arrow(first,second))

import Debug.Trace

--command line options
data Command w
  = Lex             { file       :: w ::: Maybe String         <?> "Path to file"
                    , sources    :: w ::: Maybe String         <?> "Path to sources .json"
                    }

  | Parse           { file       :: w ::: Maybe String         <?> "Path to file"
                    , sources    :: w ::: Maybe String         <?> "Path to sources .json"
                    }

  | Type            { file       :: w ::: Maybe String         <?> "Path to file"
                    , sources    :: w ::: Maybe String         <?> "Path to sources .json"
                    , solver     :: w ::: Maybe Text           <?> "SMT solver: cvc5 (default) or z3"
                    , smttimeout :: w ::: Maybe Integer        <?> "Timeout given to SMT solver in milliseconds (default: 20000)"
                    , debug      :: w ::: Bool                 <?> "Print verbose SMT output (default: False)"
                    }

  | Prove           { file       :: w ::: Maybe String         <?> "Path to file"
                    , sources    :: w ::: Maybe String         <?> "Path to sources .json"
                    , solver     :: w ::: Maybe Text           <?> "SMT solver: cvc5 (default) or z3"
                    , smttimeout :: w ::: Maybe Integer        <?> "Timeout given to SMT solver in milliseconds (default: 20000)"
                    , debug      :: w ::: Bool                 <?> "Print verbose SMT output (default: False)"
                    }

  | Coq             { file       :: w ::: Maybe String         <?> "Path to file"
                    , sources    :: w ::: Maybe String         <?> "Path to sources .json"
                    , solver     :: w ::: Maybe Text           <?> "SMT solver: cvc5 (default) or z3"
                    , smttimeout :: w ::: Maybe Integer        <?> "Timeout given to SMT solver in milliseconds (default: 20000)"
                    , debug      :: w ::: Bool                 <?> "Print verbose SMT output (default: False)"
                    }

  | HEVM            { spec       :: w ::: Maybe String         <?> "Path to spec"
                    , sol        :: w ::: Maybe String         <?> "Path to .sol"
                    , vy         :: w ::: Maybe String         <?> "Path to .vy"
                    , code       :: w ::: Maybe String         <?> "Runtime code"
                    , initcode   :: w ::: Maybe String         <?> "Initial code"
                    , layout     :: w ::: Maybe String         <?> "Storage Layout model: Solidity or Vyper"
                    , sources    :: w ::: Maybe String         <?> "Path to sources .json"
                    , solver     :: w ::: Maybe Text           <?> "SMT solver: cvc5 (default) or z3"
                    , smttimeout :: w ::: Maybe Integer        <?> "Timeout given to SMT solver in milliseconds (default: 20000)"
                    , debug      :: w ::: Bool                 <?> "Print verbose SMT output (default: False)"
                    }
  | Decompile       { solFile    :: w ::: String               <?> "Path to .sol"
                    , contract   :: w ::: String               <?> "Contract name"
                    , solver     :: w ::: Maybe Text           <?> "SMT solver: cvc5 (default) or z3"
                    , smttimeout :: w ::: Maybe Integer        <?> "Timeout given to SMT solver in milliseconds (default: 20000)"
                    , debug      :: w ::: Bool                 <?> "Print verbose SMT output (default: False)"
                    }
 deriving (Generic)

deriving instance ParseField [(Id, String)]
instance ParseRecord (Command Wrapped)
deriving instance Show (Command Unwrapped)


-----------------------
-- *** Dispatch *** ---
-----------------------


main :: IO ()
main = do
    cmd <- unwrapRecord "Act -- Smart contract specifier"
    case cmd of
      Lex f json -> lex' f json
      Parse f json -> parse' f json
      Type f json solver' smttimeout' debug' -> do
        solver'' <- parseSolver solver'
        type' f json solver'' smttimeout' debug'
      Prove file' json solver' smttimeout' debug' -> do
        solver'' <- parseSolver solver'
        prove file' json solver'' smttimeout' debug'
      Coq f json solver' smttimeout' debug' -> do
        solver'' <- parseSolver solver'
        coq' f json solver'' smttimeout' debug'
      HEVM spec' sol' vy' code' initcode' layout' sources' solver' smttimeout' debug' -> do
        solver'' <- parseSolver solver'
        hevm spec' sol' vy' code' initcode' layout' sources' solver'' smttimeout' debug'
      Decompile sol' contract' solver' smttimeout' debug' -> do
        solver'' <- parseSolver solver'
        decompile' sol' (Text.pack contract') solver'' smttimeout' debug'


---------------------------------
-- *** CLI implementation *** ---
---------------------------------


lex' :: Maybe FilePath -> Maybe FilePath -> IO ()
lex' f json = do
  (fs, _) <- processSources json f Nothing Nothing Nothing Nothing Nothing
  contents <- mapM readFile fs
  print $ lexer <$> contents

parse' :: Maybe FilePath -> Maybe FilePath -> IO ()
parse' f json = do
  (fs, _) <- processSources json f Nothing Nothing Nothing Nothing Nothing
  contents <- flip zip fs <$> mapM readFile fs
  let parsed = traverse (\(content,source) -> (,source) <$> (errorSource source $ parse $ lexer content)) contents
  validation (prettyErrs contents) print parsed

type' :: Maybe FilePath -> Maybe FilePath -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
type' f json solver' smttimeout' debug' = do
  -- contents <- readFile f
  (fs, _) <- processSources json f Nothing Nothing Nothing Nothing Nothing
  contents <- flip zip fs <$> mapM readFile fs
  proceed contents (compile contents) $ \(spec', cnstrs) -> do
    checkTypeConstraints contents solver' smttimeout' debug' cnstrs
    checkUpdateAliasing spec' solver' smttimeout' debug'
    B.putStrLn $ encode spec'

parseSolver :: Maybe Text -> IO Solvers.Solver
parseSolver s = case s of
                  Nothing -> pure Solvers.CVC5
                  Just s' -> case Text.unpack s' of
                              "z3" -> pure Solvers.Z3
                              "cvc5" -> pure Solvers.CVC5
                              "bitwuzla" -> pure Solvers.Bitwuzla
                              input -> render (text $ "unrecognised solver: " <> Text.pack input) >> exitFailure

prove :: Maybe FilePath -> Maybe FilePath -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
prove _ _ _ _ = error "SMT TBD"

checkTypeConstraints :: [(String, FilePath)] -> Solvers.Solver -> Maybe Integer -> Bool -> [Constraint Timed] -> IO ()
checkTypeConstraints contents solver' smttimeout' debug' cnstrs = do
  errs <- checkEntailment solver' smttimeout' debug' cnstrs
  proceed contents errs $ \_ -> pure ()

{-
prove file' solver' smttimeout' debug' = do
  let config = SMT.SMTConfig solver' (fromMaybe 20000 smttimeout') debug'
  contents <- readFile file'
  proceed contents (addBounds <$> compile contents) $ \claims -> do
    --checkArrayBounds claims solver' smttimeout' debug'
    checkCases claims solver' smttimeout' debug'
    --checkRewriteAliasing claims solver' smttimeout' debug'
    let
      catModels results = [m | Sat m <- results]
      catErrors results = [e | e@SMT.Error {} <- results]
      catUnknowns results = [u | u@SMT.Unknown {} <- results]

      (<->) :: DocAnsi -> [DocAnsi] -> DocAnsi
      x <-> y = x <$$> line <> (indent 2 . vsep $ y)

      failMsg :: [SMT.SMTResult] -> DocAnsi
      failMsg results
        | not . null . catUnknowns $ results
            = text "could not be proven due to a" <+> (yellow . text $ "solver timeout")
        | not . null . catErrors $ results
            = (red . text $ "failed") <+> "due to solver errors:" <-> ((fmap viaShow) . catErrors $ results)
        | otherwise
            = (red . text $ "violated") <> colon <-> (fmap prettyAnsi . catModels $ results)

      passMsg :: DocAnsi
      passMsg = (green . text $ "holds") <+> (bold . text $ "∎")

      accumulateResults :: (Bool, DocAnsi) -> (Query, [SMT.SMTResult]) -> (Bool, DocAnsi)
      accumulateResults (status, report) (query, results) = (status && holds, report <$$> msg <$$> smt)
        where
          holds = all isPass results
          msg = identifier query <+> if holds then passMsg else failMsg results
          smt = if debug' then line <> getSMT query else emptyDoc

    solverInstance <- spawnSolver config
    pcResults <- mapM (runQuery solverInstance) (mkPostconditionQueries claims)
    invResults <- mapM (runQuery solverInstance) (mkInvariantQueries claims)
    stopSolver solverInstance

    let
      invTitle = line <> (underline . bold . text $ "Invariants:") <> line
      invOutput = foldl' accumulateResults (True, emptyDoc) invResults

      pcTitle = line <> (underline . bold . text $ "Postconditions:") <> line
      pcOutput = foldl' accumulateResults (True, emptyDoc) pcResults

    render $ vsep
      [ ifExists invResults invTitle
      , indent 2 $ snd invOutput
      , ifExists pcResults pcTitle
      , indent 2 $ snd pcOutput
      ]

    unless (fst invOutput && fst pcOutput) exitFailure
    -}


coq' :: Maybe FilePath -> Maybe FilePath -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
coq' f json solver' smttimeout' debug' = do
  (fs, _) <- processSources json f Nothing Nothing Nothing Nothing Nothing
  contents <- flip zip fs <$> mapM readFile fs
  proceed contents (compile contents) $ \(spec', cnstrs) -> do
    checkTypeConstraints contents solver' smttimeout' debug' cnstrs
    --checkRewriteAliasing claims solver' smttimeout' debug'
    TIO.putStr $ coq spec'

decompile' :: FilePath -> Text -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
decompile' _ _ _ _ _ = error "Decompile TBD"
{-
decompile' solFile' cid solver' timeout debug' = do
  let config = if debug' then debugActConfig else defaultActConfig
  cores <- fmap fromIntegral getNumProcessors
  json <- flip (solc Solidity) False =<< TIO.readFile solFile'
  let (Contracts contracts, _, _) = fromJust $ readStdJSON json
  case Map.lookup ("hevm.sol:" <> cid) contracts of
    Nothing -> do
      putStrLn "compilation failed"
      exitFailure
    Just c -> do
      res <- runEnv (Env config) $ Solvers.withSolvers solver' cores 1 (naturalFromInteger <$> timeout) $ \solvers -> decompile c solvers
      case res of
        Left e -> do
          TIO.putStrLn e
          exitFailure
        Right s -> do
          putStrLn (prettyAct s)
-}

hevm :: Maybe FilePath -> Maybe FilePath -> Maybe FilePath -> Maybe String -> Maybe String -> Maybe String -> Maybe FilePath -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
hevm actspec sol' vy' code' initcode' layout' sources' solver' timeout debug' = do
  let config = if debug' then debugActConfig else defaultActConfig
  cores <- liftM fromIntegral getNumProcessors
  (actspecs, inputsMap) <- processSources sources' actspec sol' vy' code' initcode' layout'
  specsContents <- flip zip actspecs <$> mapM readFile actspecs
  proceed specsContents (compile specsContents) $ \(Act store contracts, constraints) -> do
    checkTypeConstraints specsContents solver' timeout debug' constraints
    cmap <- createContractMap contracts inputsMap
    res <- runEnv (Env config) $ Solvers.withSolvers solver' cores 1 (naturalFromInteger <$> timeout) $ \solvers ->
      checkContracts solvers store cmap
    case res of
      Success _ -> pure ()
      Failure err -> prettyErrs [("","")] (second ("",) <$> err)
  where

    -- Creates maps of storage layout modes and bytecodes, for all contracts contained in the given Act specification
    createContractMap :: [Contract] -> Map (Maybe Id) (LayoutMode, ByteString, ByteString) -> IO (Map Id (Contract, BS.ByteString, BS.ByteString, LayoutMode))
    createContractMap contracts inputsMap | Map.keys inputsMap == [Nothing] =
      case contracts of
        [spec'@(Contract _ cnstr _)] -> do
          let cid =  _cname cnstr
              (layout'', initcode'', runtimecode') = fromJust $ Map.lookup Nothing inputsMap
          pure (Map.singleton cid (spec', initcode'', runtimecode', layout''))
        _ -> render (text "Specification contains multiple contracts, while a single bytecode object is given" <> line) >> exitFailure
    createContractMap contracts inputsMap = do
      pure $ foldr (\spec'@(Contract _ cnstr _) cmap ->
                let cid =  _cname cnstr
                    (layoutMode, initcode'', runtimecode') = fromMaybe (error $ "Contract " <> cid <> " not found in sources") $ Map.lookup (Just cid) inputsMap
                in (Map.insert cid (spec', initcode'', runtimecode', layoutMode) cmap)
             ) mempty contracts

-- In case of Failue print errors, else return value
validationErrIO :: Show e => Validation (NonEmpty e) a -> IO a
validationErrIO v = validation (\e -> (render $ text "Errors in json:") >> (mapM_ (render . (<> line) . text . Text.pack . show) e) >> exitFailure) pure v

-- Creates a map of information for contracts available from source code or bytecode arguments
processSources :: Maybe FilePath -> Maybe FilePath -> Maybe FilePath -> Maybe FilePath -> Maybe String -> Maybe String -> Maybe String -> IO ([FilePath], (Map (Maybe Id) (LayoutMode, ByteString, ByteString)))
processSources sources' actspec sol' vy' code' initcode' layout' =
  case (sources', actspec, sol', vy', code', initcode', layout') of
    (Just f, Nothing, Nothing, Nothing, Nothing, Nothing, Nothing) -> do
      jsonContents  <- TIO.readFile f
      (specs, maybeContractSrcs, maybeSrcsWithLangs) <-
            case readSourcesJSON jsonContents of
              Right res -> pure res
              Left err -> render (text ("Error when parsing json:") <> line <> text (Text.pack err) <> line) >> exitFailure
      let specs' = locateSpecs f specs
      contractSources <- maybe (render (text "Missing \"contracts\" object, which maps contracts to their implementation source" <> line) >> exitFailure) pure maybeContractSrcs
      contractMap <- Map.fromList <$> forM (Map.toList contractSources) (\(cid, info) ->
        case info of
          (Just src, Nothing, Nothing, Nothing) ->
              let src' = Text.unpack src
                  cid' = Text.unpack cid
              in do
              sourcesWithLangs <- maybe (render (text "Missing \"sources\" object, which maps sources to their language/layout" <> line) >> exitFailure) pure maybeSrcsWithLangs
              srcsWithLayouts <- validationErrIO $ traverse checkLanguage sourcesWithLangs
              -- TODO: compile once, not for every contract
              bytecodeMap <- compileSources f srcsWithLayouts
              sourceMap <- maybe (render (text ("Source " <> src <> " of " <> cid <> " not found in sources") <> line) >> exitFailure) pure $ Map.lookup src' bytecodeMap
              layoutMode <- maybe (render (text ("Source " <> src <> " of " <> cid <> " not found in sources") <> line) >> exitFailure) pure $ Map.lookup src srcsWithLayouts
              (initcode'', runtimecode') <- case layoutMode of
                SolidityLayout -> maybe (error $ "Contract " <> cid' <> " not found in " <> src') pure $ Map.lookup (Just cid') sourceMap
                VyperLayout -> pure $ fromJust $ Map.lookup Nothing sourceMap
              pure (Just cid', (layoutMode, initcode'', runtimecode'))
          (Nothing, Nothing, Just _, _) -> render (text ("No runtime code is given for contract " <> cid) <> line) >> exitFailure
          (Nothing, Just _, Nothing, _) -> render (text ("No initcode code is given for contract " <> cid) <> line) >> exitFailure
          (Nothing, Just _, Just _, Nothing) -> render (text ("No layout mode specified for contract " <> cid <> ". Options: Solidity, Vyper") <> line) >> exitFailure
          (Nothing, Just runtimecodeFile, Just initcodeFile, Just layout'') -> do
              layout''' <- validationErrIO $ checkLanguage layout''
              initcode'' <- toCode (Text.unpack initcodeFile) <$> (TIO.readFile $ Text.unpack initcodeFile)
              runtimecode' <- toCode (Text.unpack runtimecodeFile) <$> (TIO.readFile $ Text.unpack runtimecodeFile)
              pure (Just $ Text.unpack cid, (layout''', initcode'', runtimecode'))
          (Nothing, Nothing, Nothing, _) -> render (text ("Both source and bytecode information given for contract " <> cid) <> line) >> exitFailure
          (Just _, _, _, _) -> render (text ("Both source and bytecode information given for contract " <> cid) <> line) >> exitFailure
            )
      pure (specs', contractMap)
    (Just _, Just _, _, _, _, _, _) -> render (text "Both a sources JSON file and Act spec file are given. Please specify only one.") >> exitFailure
    (Just _, _, Just _, _, _, _, _) -> render (text "Both a sources JSON file and Solidity file are given. Please specify only one.") >> exitFailure
    (Just _, _, _, Just _, _, _, _) -> render (text "Both a sources JSON file and Vyper file are given. Please specify only one.") >> exitFailure
    (Just _, _, _, _, Just _, _, _) -> render (text "Both a sources JSON file and runtime code are given. Please specify only one.") >> exitFailure
    (Just _, _, _, _, _, Just _, _) -> render (text "Both a sources JSON file and initcode code are given. Please specify only one.") >> exitFailure
    (Nothing, Nothing, _, _, _, _, _) -> render (text "No Act specification is given" <> line) >> exitFailure
    (Nothing, Just a, Just f, Nothing, Nothing, Nothing, Nothing) -> do
      bcs <- bytecodes f SolidityLayout
      pure ([a], Map.map (\(b1,b2) -> (SolidityLayout, b1, b2)) bcs)
    (Nothing, _, Just _, Just _, _, _, _) -> render (text "Both Solidity and Vyper file are given. Please specify only one." <> line) >> exitFailure
    (Nothing, _, Just _, _, Just _, _, _) -> render (text "Both Solidity file and runtime code are given. Please specify only one." <> line) >> exitFailure
    (Nothing, _, Just _, _, _, Just _, _) -> render (text "Both Solidity file and initial code are given. Please specify only one." <> line) >> exitFailure
    (Nothing, Just a, Nothing, Just f, Nothing, Nothing, Nothing) -> do
      bcs <- bytecodes f VyperLayout
      pure ([a], Map.map (\(b1,b2) -> (VyperLayout, b1, b2)) bcs)
    (Nothing, _, Nothing, Just _, Just _, _, _) -> render (text "Both Vyper file and runtime code are given. Please specify only one." <> line) >> exitFailure
    (Nothing, _, Nothing, Just _, _, Just _, _) -> render (text "Both Vyper file and initial code are given. Please specify only one." <> line) >> exitFailure
    (Nothing, _, Nothing, Nothing, Nothing, _, _) -> render (text "No runtime code is given" <> line) >> exitFailure
    (Nothing, _, Nothing, Nothing, _, Nothing, _) -> render (text "No initial code is given" <> line) >> exitFailure
    (Nothing, Just _, Nothing, Nothing, Just _, Just _, Nothing) -> render (text "Missing storage layout mode. Use --layout with options: Solidity or Vyper" <> line) >> exitFailure
    (Nothing, Just a, Nothing, Nothing, Just run, Just initc, Just layout'') -> do
      layout''' <- validationErrIO $ checkLanguage $ Text.pack layout''
      pure ([a], Map.singleton Nothing (layout''', toCode "bytecode" (Text.pack initc), toCode "bytecode" (Text.pack run)))
    (_,_,_,_,Nothing,Nothing, Just _) -> render (text "Option --layout given, but --code and --initcode are not used" <> line) >> exitFailure


maybeEither :: Maybe (Either a b) -> Either a (Maybe b)
maybeEither Nothing = Right Nothing
maybeEither (Just e) = Just <$> e

type SourceInfoMap = Map Text Text
type ContractInfoMap = Map Text (Maybe Text, Maybe Text, Maybe Text, Maybe Text)

readSourcesJSON :: Text -> Either String ([Text], Maybe ContractInfoMap, Maybe SourceInfoMap)
readSourcesJSON json = case eitherDecode $ BS.fromStrict $ encodeUtf8 json of
  Left s -> error s
  Right decoded -> do
    (specs, contractSourcesObj, sourceLangsObj) <- flip parseEither decoded $ \obj -> do
      specs <- obj .: "specifications"
      contracts <- obj .:? "contracts"
      srcs <- obj .:? "sources"
      pure (specs, contracts, srcs)
    contractSources <- maybeEither $ fmap (sequence . Map.map (parseEither (\obj -> do
        src <- obj .:? "source"
        code' <- obj .:? "code"
        initc <- obj .:? "initcode"
        layout' <- obj .:? "layout"
        pure (src, code', initc, layout')
      ))) contractSourcesObj
    sourceLangs <- maybeEither $ fmap (sequence . Map.map (parseEither (.: "language"))) sourceLangsObj
    pure (specs, contractSources, sourceLangs)

locateSpecs :: FilePath -> [Text] -> [FilePath]
locateSpecs jsonPath specs = ((</>) (takeDirectory jsonPath) . Text.unpack) <$> specs

checkLanguage :: Text -> Validation (NonEmpty Text) LayoutMode
checkLanguage "Solidity" = Success SolidityLayout
checkLanguage "Vyper" = Success VyperLayout
checkLanguage _ = Failure ["Unknown language"]

-- Compiles all source files provided in the sources .json file
-- Returns map from source filepaths to maps from included contract IDs to bytecodes
compileSources :: FilePath -> Map Text LayoutMode -> IO (Map FilePath (Map (Maybe Id) (BS.ByteString, BS.ByteString)))
compileSources jsonPath jsonMap =
  sequence $ Map.fromList $ map (\(src, layoutMode) ->
    let jsonDir = takeDirectory jsonPath
        src' = jsonDir </> Text.unpack src
    in (Text.unpack src, bytecodes src' layoutMode)) $ Map.toList jsonMap

-- Compiles a source file to bytecode. Returns map from included contract IDs to bytecodes.
-- Mapping from (Maybe Id) to cover the case where a single Vyper file is given, which provides no information on contract names.
bytecodes :: FilePath -> LayoutMode -> IO (Map (Maybe Id) (BS.ByteString, BS.ByteString))
bytecodes srcFile SolidityLayout = do
  src <- TIO.readFile srcFile
  json <- solc Solidity src False
  (Contracts sol', _, _) <- maybe (render (text ("Compilation of Solidity source \"" <> Text.pack srcFile <> "\" failed") <> line) >> exitFailure) pure (readStdJSON json)
  pure $ Map.fromList $ map (\(fn,c) -> (Just $ Text.unpack $ snd $ Text.breakOnEnd ":" fn, (c.creationCode, c.runtimeCode))) $ Map.toList sol'
bytecodes srcFile VyperLayout = Map.singleton Nothing <$> vyper srcFile

-- Compile vyper source file
vyper :: FilePath -> IO (BS.ByteString, BS.ByteString)
vyper src = do
  -- Must drop initial "0x" and trailing "\n"
  bc <- toCode src . Text.pack <$> (readProcess "vyper" ["-f", "bytecode", src] [])
  bcr <- toCode src . Text.pack <$> (readProcess "vyper" ["-f", "bytecode_runtime", src] [])
  pure (bc, bcr)

-- Convert bytecode from hex string representation to binary
toCode :: FilePath -> Text -> ByteString
toCode fromFile t = case BS16.decodeBase16Untyped (encodeUtf8 (stripSuffixIf "\n" $ stripPrefixIf "0x" t)) of
  Right d -> d
  Left e -> if containsLinkerHole t
            then error ("Error toCode: unlinked libraries detected in bytecode, in " <> fromFile)
            else error ("Error toCode:" <> Text.unpack e <> ", in " <> fromFile)
  where
    stripSuffixIf s txt = fromMaybe txt $ Text.stripSuffix s txt
    stripPrefixIf s txt = fromMaybe txt $ Text.stripPrefix s txt

-------------------
-- *** Util *** ---
-------------------

-- | Fail on error, or proceed with continuation
proceed :: Validate err => [(String,FilePath)] -> err (NonEmpty (Pn, (FilePath, String))) a -> (a -> IO ()) -> IO ()
proceed contents comp continue = validation (prettyErrs contents) continue (comp ^. revalidate)

compile :: [(String, FilePath)] -> Error (FilePath ,String) (Act, [Constraint Timed])
compile = pure . (first annotate) <==< pure . (\(acts, cnstr) -> (acts, (checkIntegerBoundsAct acts) ++ cnstr))
  <==< typecheck <==< (traverse (\(content, src) -> (,src) <$> (errorSource src $ parse $ lexer content)))

