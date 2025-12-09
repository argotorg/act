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
import Act.Bounds
import Act.SMT as SMT
import Act.Type
import Act.Coq hiding (indent, (<+>))
import Act.HEVM
import Act.HEVM_utils
import Act.Consistency
import Act.Print
import Act.Lex (lastPos)
--import Act.Decompile

import qualified EVM.Solvers as Solvers
import EVM.Solidity
import EVM.Effects

--command line options
data Command w
  = Lex             { file       :: w ::: String               <?> "Path to file"}

  | Parse           { file       :: w ::: String               <?> "Path to file"}

  | Type            { file       :: w ::: String               <?> "Path to file"
                    , solver     :: w ::: Maybe Text           <?> "SMT solver: cvc5 (default) or z3"
                    , smttimeout :: w ::: Maybe Integer        <?> "Timeout given to SMT solver in milliseconds (default: 20000)"
                    , debug      :: w ::: Bool                 <?> "Print verbose SMT output (default: False)"
                    }

  | Prove           { file       :: w ::: String               <?> "Path to file"
                    , solver     :: w ::: Maybe Text           <?> "SMT solver: cvc5 (default) or z3"
                    , smttimeout :: w ::: Maybe Integer        <?> "Timeout given to SMT solver in milliseconds (default: 20000)"
                    , debug      :: w ::: Bool                 <?> "Print verbose SMT output (default: False)"
                    }

  | Coq             { file       :: w ::: String               <?> "Path to file"
                    , solver     :: w ::: Maybe Text           <?> "SMT solver: cvc5 (default) or z3"
                    , smttimeout :: w ::: Maybe Integer        <?> "Timeout given to SMT solver in milliseconds (default: 20000)"
                    , debug      :: w ::: Bool                 <?> "Print verbose SMT output (default: False)"
                    }

  | HEVM            { spec       :: w ::: Maybe String         <?> "Path to spec"
                    , sol        :: w ::: Maybe String         <?> "Path to .sol"
                    , vy         :: w ::: Maybe String         <?> "Path to .vy"
                    , code       :: w ::: Maybe ByteString     <?> "Runtime code"
                    , initcode   :: w ::: Maybe ByteString     <?> "Initial code"
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
      Lex f -> lex' f
      Parse f -> parse' f
      Type f solver' smttimeout' debug' -> do
        solver'' <- parseSolver solver'
        type' f solver'' smttimeout' debug'
      Prove file' solver' smttimeout' debug' -> do
        solver'' <- parseSolver solver'
        prove file' solver'' smttimeout' debug'
      Coq f solver' smttimeout' debug' -> do
        solver'' <- parseSolver solver'
        coq' f solver'' smttimeout' debug'
      HEVM spec' sol' vy' code' initcode' sources' solver' smttimeout' debug' -> do
        solver'' <- parseSolver solver'
        hevm spec' sol' vy' code' initcode' sources' solver'' smttimeout' debug'
      Decompile sol' contract' solver' smttimeout' debug' -> do
        solver'' <- parseSolver solver'
        decompile' sol' (Text.pack contract') solver'' smttimeout' debug'


---------------------------------
-- *** CLI implementation *** ---
---------------------------------


lex' :: FilePath -> IO ()
lex' f = do
  contents <- readFile f
  print $ lexer contents

parse' :: FilePath -> IO ()
parse' f = do
  contents <- readFile f
  validation (prettyErrs contents) print (parse $ lexer contents)

type' :: FilePath -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
type' f solver' smttimeout' debug' = do
  contents <- readFile f
  proceed contents (addBounds <$> compile contents) $ \claims -> do
    --checkArrayBounds claims solver' smttimeout' debug'
    -- checkCases claims solver' smttimeout' debug'
    --checkRewriteAliasing claims solver' smttimeout' debug'
    B.putStrLn $ encode claims

parseSolver :: Maybe Text -> IO Solvers.Solver
parseSolver s = case s of
                  Nothing -> pure Solvers.CVC5
                  Just s' -> case Text.unpack s' of
                              "z3" -> pure Solvers.Z3
                              "cvc5" -> pure Solvers.CVC5
                              "bitwuzla" -> pure Solvers.Bitwuzla
                              input -> render (text $ "unrecognised solver: " <> Text.pack input) >> exitFailure

prove :: FilePath -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
prove _ _ _ _ = error "SMT TBD"
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


coq' :: FilePath -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
coq' f solver' smttimeout' debug' = do
  contents <- readFile f
  proceed contents (compile contents) $ \claims -> do
    --checkArrayBounds claims solver' smttimeout' debug'
    --checkCases claims solver' smttimeout' debug'
    --checkRewriteAliasing claims solver' smttimeout' debug'
    TIO.putStr $ coq claims

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

hevm :: Maybe FilePath -> Maybe FilePath -> Maybe FilePath -> Maybe ByteString -> Maybe ByteString -> Maybe FilePath -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
hevm actspec sol' vy' code' initcode' sources' solver' timeout debug' = do
  let config = if debug' then debugActConfig else defaultActConfig
  cores <- liftM fromIntegral getNumProcessors
  (actspecs, inputsMap) <- processSources
  specsContents <- intercalate "\n" <$> traverse readFile actspecs
  proceed specsContents (addBounds <$> compile specsContents) $ \ (Act store contracts) -> do
    cmap <- createContractMap contracts inputsMap
    res <- runEnv (Env config) $ Solvers.withSolvers solver' cores 1 (naturalFromInteger <$> timeout) $ \solvers ->
      checkContracts solvers store cmap
    case res of
      Success _ -> pure ()
      Failure err -> prettyErrs "" err
  where

    -- Creates maps of storage layout modes and bytecodes, for all contracts contained in the given Act specification
    createContractMap :: [Contract] -> Map (Maybe Id) (LayoutMode, ByteString, ByteString) -> IO (Map Id (Contract, BS.ByteString, BS.ByteString, LayoutMode))
    createContractMap contracts inputsMap | Map.keys inputsMap == [Nothing] =
      -- Singleton inputsMap with Nothing as contract Id means that '--vy' was given
      case contracts of
        [spec'@(Contract cnstr _)] -> do
          let cid =  _cname cnstr
              (_, initcode'', runtimecode') = fromJust $ Map.lookup Nothing inputsMap
          pure (Map.singleton cid (spec', initcode'', runtimecode', VyperLayout))
        _ -> render (text "Vyper file represents a single contract, while specification contains multiple contracts" <> line) >> exitFailure
    createContractMap contracts inputsMap = do
      pure $ foldr (\spec'@(Contract cnstr _) cmap ->
                let cid =  _cname cnstr
                    (layoutMode, initcode'', runtimecode') = fromMaybe (error $ "Contract " <> cid <> "not found in sources") $ Map.lookup (Just cid) inputsMap
                in (Map.insert cid (spec', initcode'', runtimecode', layoutMode) cmap)
             ) mempty contracts

    -- Creates a map of information for contracts available from source code or bytecode arguments
    processSources :: IO ([FilePath], Map (Maybe Id) (LayoutMode, ByteString, ByteString))
    processSources =
      case (sources', actspec, sol', vy', code', initcode') of
        (Just f, Nothing, Nothing, Nothing, Nothing, Nothing) -> do
          jsonContents  <- TIO.readFile f
          let (specs, contractSources, sourceLangs) =
                case readSourcesJSON jsonContents of
                  Right res -> res
                  Left err -> error err
          let specs' = locateSpecs f specs
          let sourceLayouts = checkLanguages sourceLangs
          bytecodeMap <- compileSources f sourceLayouts
          let contractMap = Map.fromList $ map (\(cid,src) ->
                      let src' = Text.unpack src
                          cid' = Text.unpack cid
                          sourceMap = fromMaybe (error $ "Source " <> Text.unpack src <> " of " <> cid' <> " not found in sources") $ Map.lookup src' bytecodeMap
                          layoutMode = fromMaybe (error $ "Source " <> Text.unpack src <> " of " <> cid' <> " not found in sources") $ Map.lookup src sourceLayouts
                          (initcode'', runtimecode') = case layoutMode of
                            SolidityLayout -> fromMaybe (error $ "Contract " <> cid' <> " not found in " <> src') $ Map.lookup (Just cid') sourceMap
                            VyperLayout -> fromJust $ Map.lookup Nothing sourceMap
                      in (Just cid', (layoutMode, initcode'', runtimecode'))) $ Map.toList contractSources
          pure (specs', contractMap)
        (Just _, Just _, _, _, _, _) -> render (text "Both a sources JSON file and Act spec file are given. Please specify only one.") >> exitFailure
        (Just _, _, Just _, _, _, _) -> render (text "Both a sources JSON file and Solidity file are given. Please specify only one.") >> exitFailure
        (Just _, _, _, Just _, _, _) -> render (text "Both a sources JSON file and Vyper file are given. Please specify only one.") >> exitFailure
        (Just _, _, _, _, Just _, _) -> render (text "Both a sources JSON file and runtime code are given. Please specify only one.") >> exitFailure
        (Just _, _, _, _, _, Just _) -> render (text "Both a sources JSON file and initcode code are given. Please specify only one.") >> exitFailure
        (Nothing, Nothing, _, _, _, _) -> render (text "No Act specification is given" <> line) >> exitFailure
        (Nothing, Just a, Just f, Nothing, Nothing, Nothing) -> do
          bcs <- bytecodes f SolidityLayout
          pure ([a], Map.map (\(b1,b2) -> (SolidityLayout, b1, b2)) bcs)
        (Nothing, _, Just _, Just _, _, _) -> render (text "Both Solidity and Vyper file are given. Please specify only one." <> line) >> exitFailure
        (Nothing, _, Just _, _, Just _, _) -> render (text "Both Solidity file and runtime code are given. Please specify only one." <> line) >> exitFailure
        (Nothing, _, Just _, _, _, Just _) -> render (text "Both Solidity file and initial code are given. Please specify only one." <> line) >> exitFailure
        (Nothing, Just a, Nothing, Just f, Nothing, Nothing) -> do
          bcs <- bytecodes f VyperLayout
          pure ([a], Map.map (\(b1,b2) -> (VyperLayout, b1, b2)) bcs)
        (Nothing, _, Nothing, Just _, Just _, _) -> render (text "Both Vyper file and runtime code are given. Please specify only one." <> line) >> exitFailure
        (Nothing, _, Nothing, Just _, _, Just _) -> render (text "Both Vyper file and initial code are given. Please specify only one." <> line) >> exitFailure
        (Nothing, _, Nothing, Nothing, Nothing, _) -> render (text "No runtime code is given" <> line) >> exitFailure
        (Nothing, _, Nothing, Nothing, _, Nothing) -> render (text "No initial code is given" <> line) >> exitFailure
        (Nothing, _, Nothing, Nothing, Just _, Just _) -> render (text "Only Solidity or Vyper files supported") >> exitFailure -- TODO pure (i, c)


readSourcesJSON :: Text -> Either String ([Text], Map Text Text, Map Text Text)
readSourcesJSON json = case eitherDecode $ BS.fromStrict $ encodeUtf8 json of
  Left s -> error s
  Right decoded -> do
    (specs, contractObjs, sourcesObjs) <- flip parseEither decoded $ \obj -> do
      specs <- obj .: "specifications"
      contractsObjs <- obj .: "contracts"
      sourcesObjs <- obj .: "sources"
      pure (specs, contractsObjs, sourcesObjs)
    contractSources <- sequence (Map.map (parseEither (.: "source")) contractObjs)
    sourceLangs  <- sequence (Map.map (parseEither (.: "language")) sourcesObjs)
    pure (specs, contractSources, sourceLangs)

locateSpecs :: FilePath -> [Text] -> [FilePath]
locateSpecs jsonPath specs = ((</>) (takeDirectory jsonPath) . Text.unpack) <$> specs

checkLanguages :: Map Text Text -> Map Text LayoutMode
checkLanguages = Map.map (fromMaybe (error "Unknown language") . checkLanguage)
  where
    checkLanguage :: Text -> Maybe LayoutMode
    checkLanguage "Solidity" = Just SolidityLayout
    checkLanguage "Vyper" = Just VyperLayout
    checkLanguage "Bytecode" = Just SolidityLayout -- TODO maybe give options
    checkLanguage _ = Nothing

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
  let (Contracts sol', _, _) = fromJust $ readStdJSON json
  pure $ Map.fromList $ map (\(fn,c) -> (Just $ Text.unpack $ snd $ Text.breakOnEnd ":" fn, (c.creationCode, c.runtimeCode))) $ Map.toList sol'
bytecodes srcFile VyperLayout = Map.singleton Nothing <$> vyper srcFile

-- Compile vyper source file
vyper :: FilePath -> IO (BS.ByteString, BS.ByteString)
vyper src = do
  -- Must drop initial "0x" and trailing "\n"
  bc <- toCode src . Text.dropEnd 1 . Text.drop 2 . Text.pack <$> (readProcess "vyper" ["-f", "bytecode", src] [])
  bcr <- toCode src . Text.dropEnd 1 . Text.drop 2 . Text.pack <$> (readProcess "vyper" ["-f", "bytecode_runtime", src] [])
  pure (bc, bcr)

-- Convert bytecode from hex string representation to binary
toCode :: FilePath -> Text -> ByteString
toCode fromFile t = case BS16.decodeBase16Untyped (encodeUtf8 t) of
  Right d -> d
  Left e -> if containsLinkerHole t
            then error ("Error toCode: unlinked libraries detected in bytecode, in " <> fromFile)
            else error ("Error toCode:" <> Text.unpack e <> ", in " <> fromFile)

-------------------
-- *** Util *** ---
-------------------

-- | Fail on error, or proceed with continuation
proceed :: Validate err => String -> err (NonEmpty (Pn, String)) a -> (a -> IO ()) -> IO ()
proceed contents comp continue = validation (prettyErrs contents) continue (comp ^. revalidate)

compile :: String -> Error String Act
compile = pure . annotate <==< fmap fst . typecheck <==< parse . lexer

prettyErrs :: Traversable t => String -> t (Pn, String) -> IO ()
prettyErrs contents errs = mapM_ prettyErr errs >> exitFailure
  where
  prettyErr (pn, msg) | pn == nowhere = do
    hPutStrLn stderr "Internal error:"
    hPutStrLn stderr msg
  prettyErr (pn, msg) | pn == lastPos = do
    let culprit = last $ lines contents
        line' = length (lines contents) - 1
        col  = length culprit
    hPutStrLn stderr $ show line' <> " | " <> culprit
    hPutStrLn stderr $ unpack (Text.replicate (col + length (show line' <> " | ") - 1) " " <> "^")
    hPutStrLn stderr msg
  prettyErr (AlexPn _ line' col, msg) = do
    let cxt = safeDrop (line' - 1) (lines contents)
    hPutStrLn stderr $ msg <> ":"
    hPutStrLn stderr $ show line' <> " | " <> head cxt
    hPutStrLn stderr $ unpack (Text.replicate (col + length (show line' <> " | ") - 1) " " <> "^")
    where
      safeDrop :: Int -> [a] -> [a]
      safeDrop 0 a = a
      safeDrop _ [] = []
      safeDrop _ [a] = [a]
      safeDrop n (_:xs) = safeDrop (n-1) xs
