{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# Language RecordWildCards #-}
{-# Language ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE KindSignatures #-}

module Act.Consistency (
  checkCases,
  checkArrayBounds,
  checkRewriteAliasing
) where


import Prelude hiding (GT, LT)

import Data.List
import Prettyprinter hiding (group)
import System.Exit (exitFailure)
import Data.Maybe
import Data.Type.Equality ((:~:)(..), TestEquality (testEquality))
import Data.Singletons (sing, SingI)
import Data.Semigroup (Arg (..))

import Control.Monad.Reader
import Control.Monad (forM, forM_, zipWithM)

import Act.Lex (AlexPosn(..))
import Act.Syntax
import Act.Syntax.TypedExplicit
import Act.SMT as SMT
import Act.Print

import qualified EVM.Solvers as Solvers

-- TODO this is duplicated in hevm Keccak.hs but not exported
combine :: [a] -> [(a,a)]
combine lst = combine' lst []
  where
    combine' [] acc = concat acc
    combine' (x:xs) acc =
      let xcomb = [ (x, y) | y <- xs] in
      combine' xs (xcomb:acc)

mkOr :: [Exp ABoolean] -> Exp ABoolean
mkOr = foldr (Or nowhere) (LitBool nowhere False)

mkOrNot :: [Exp ABoolean] -> Exp ABoolean
mkOrNot = foldr (Or nowhere . Neg nowhere) (LitBool nowhere False)

-- | Checks non-overlapping cases,
-- For every pair of case conditions we assert that they are true
-- simultaneously. The query must be unsat.
mkNonoverlapAssertion :: [Exp ABoolean] -> Exp ABoolean
mkNonoverlapAssertion caseconds =
  mkOr $ (uncurry $ And nowhere) <$> combine caseconds

-- | Checks exhaustiveness of cases.
-- We assert that none of the case conditions are true at the same
-- time. The query must be unsat.
mkExhaustiveAssertion :: [Exp ABoolean] -> Exp ABoolean
mkExhaustiveAssertion caseconds =
  foldl mkAnd (LitBool nowhere True) caseconds
  where
    mkAnd r c = And nowhere (Neg nowhere c) r

-- | Create a query for cases
mkCaseQuery :: ([Exp ABoolean] -> Exp ABoolean) -> [Behaviour] -> (Id, SMTExp, (SolverInstance -> IO Model))
mkCaseQuery props behvs@((Behaviour _ _ (Interface ifaceName decls) preconds _ _ _ _):_) =
  (ifaceName, smt, getModel)
  where
    locs = nub $ concatMap locsFromExp (preconds <> caseconds)
    (slocs, clocs) = partitionLocs locs
    env = concatMap ethEnvFromBehaviour behvs
    pres = mkAssert ifaceName <$> preconds
    caseconds = concatMap _caseconditions behvs

    smt = SMTExp
      { _storage = concatMap (declareLocation ifaceName) slocs
      , _calldata = (declareArg ifaceName <$> decls) <> concatMap (declareLocation ifaceName) clocs
      , _environment = declareEthEnv <$> env
      , _assertions = (mkAssert ifaceName $ props caseconds) : pres
      }

    getModel solver = do
      prestate <- mapM (getLocationValue solver ifaceName Pre) slocs
      calldata <- mapM (getCalldataValue solver ifaceName) decls
      calllocs <- mapM (getLocationValue solver ifaceName Pre) clocs
      environment <- mapM (getEnvironmentValue solver) env
      pure $ Model
        { _mprestate = prestate
        , _mpoststate = []
        , _mcalldata = (ifaceName, calldata)
        , _mcalllocs = calllocs
        , _menvironment = environment
        , _minitargs = []
        }
mkCaseQuery _ [] = error "Internal error: behaviours cannot be empty"

-- | Checks nonoverlapping and exhaustiveness of cases
checkCases :: Act -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
checkCases (Act _ contracts) solver' smttimeout debug = do
  let groups = concatMap (\(Contract _ behvs) -> groupBy sameIface behvs) contracts
  let config = SMT.SMTConfig solver' (fromMaybe 20000 smttimeout) debug
  solver <- spawnSolver config
  let qs = mkCaseQuery mkNonoverlapAssertion <$> groups
  r <- forM qs (\(name, q, getModel) -> do
                        res <- checkSat solver getModel q
                        pure (name, res))
  mapM_ (checkRes "nonoverlapping") r
  let qs' = mkCaseQuery mkExhaustiveAssertion <$> groups
  r' <- forM qs' (\(name, q, getModel) -> do
                          res <- checkSat solver getModel q
                          pure (name, res))
  mapM_ (checkRes "exhaustive") r'

    where

      sameIface (Behaviour _ _ iface _ _ _ _ _) (Behaviour _ _ iface' _ _ _ _ _) =
        makeIface iface == makeIface iface'

      checkRes :: String -> (Id, SMT.SMTResult) -> IO ()
      checkRes check (name, res) =
        case res of
          Sat model -> failMsg ("Cases are not " <> check <> " for behavior " <> name <> ".") (prettyAnsi model)
          Unsat -> pure ()
          Unknown -> errorMsg $ "Solver timeour. Cannot prove that cases are " <> check <> " for behavior " <> name <> "."
          SMT.Error _ err -> errorMsg $ "Solver error: " <> err <> "\nCannot prove that cases are " <>  check <> " for behavior " <> name <> "."

      failMsg str model = render (red (pretty str) <> line <> model <> line) >> exitFailure
      errorMsg str = render (pretty str <> line) >> exitFailure


--- ** Array Bounds Checking ** ---

type ModelCtx = Reader Model

mkBounds :: TypedExp -> Int -> [Exp ABoolean]
mkBounds (TExp SInteger _ e) b = [LEQ nowhere (LitInt nowhere 0) e, LT nowhere e (LitInt nowhere $ toInteger b)]
mkBounds _ _ = error "Internal Error: Expected Integral Index"

mkRefBounds :: Ref a -> [Exp ABoolean]
mkRefBounds (SArray _ ref _ tes) = concatMap (uncurry mkBounds) tes <> mkRefBounds ref
mkRefBounds (SMapping _ ref _ _) = mkRefBounds ref
mkRefBounds (SField _ ref _ _) = mkRefBounds ref
mkRefBounds _ = []

mkStorageBounds :: Location -> [Exp ABoolean]
mkStorageBounds (Loc _ _ (Item _ _ ref)) = mkRefBounds ref

-- TODO: There are locs that don't need to be checked, e.g. assignment locs cannot be out of bounds
mkConstrArrayBoundsQuery :: Constructor -> (Id, [Location], SMTExp, SolverInstance -> IO Model)
mkConstrArrayBoundsQuery constructor@(Constructor _ (Interface ifaceName decls) preconds _ _ initialStorage) =
  (ifaceName, arrayLocs, smt, getModel)
  where
    -- Declare vars
    activeLocs = locsFromConstructor constructor
    envs = ethEnvFromConstructor constructor

    arrayLocs = filter (\(Loc _ _ item) -> isArrayItem item && posnFromItem item /= nowhere) activeLocs
    boundsExps = concatMap mkStorageBounds arrayLocs
    assertion = mkOrNot boundsExps

    (activeSLocs, activeCLocs) = partitionLocs activeLocs
    smt = mkDefaultSMT True activeSLocs activeCLocs envs ifaceName decls preconds [] initialStorage assertion

    getModel = getCtorModel constructor

mkBehvArrayBoundsQuery :: Behaviour -> (Id, [Location], SMTExp, SolverInstance -> IO Model)
mkBehvArrayBoundsQuery behv@(Behaviour _ _ (Interface ifaceName decls) preconds caseconds _ stateUpdates _) =
  (ifaceName, arrayLocs, smt, getModel)
  where
    -- Declare vars
    activeLocs = locsFromBehaviour behv
    envs = ethEnvFromBehaviour behv

    arrayLocs = filter (\(Loc _ _ item) -> isArrayItem item && posnFromItem item /= nowhere) activeLocs
    boundsExps = concatMap mkStorageBounds arrayLocs
    assertion = mkOrNot boundsExps

    (activeSLocs, activeCLocs) = partitionLocs activeLocs
    smt = mkDefaultSMT False activeSLocs activeCLocs envs ifaceName decls preconds caseconds stateUpdates assertion

    getModel = getPostconditionModel (Behv behv)

checkArrayBounds :: Act -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
checkArrayBounds (Act _ contracts)  solver' smttimeout debug =
  forM_ contracts (\(Contract constr behvs) -> do
    let config = SMT.SMTConfig solver' (fromMaybe 20000 smttimeout) debug
    solver <- spawnSolver config
    let constrQs = mkConstrArrayBoundsQuery constr
    let behvQs = mkBehvArrayBoundsQuery <$> behvs

    r <- (\(name, locs, q, getModel) -> do
                          res <- checkSat solver getModel q
                          pure (name, locs, res)) constrQs
    checkRes "Constructor" r
    r' <- forM behvQs (\(name, locs, q, getModel) -> do
                          res <- checkSat solver getModel q
                          pure (name, locs, res))
    mapM_ (checkRes "behaviour") r' )
  where
    checkRes :: String -> (Id, [Location], SMT.SMTResult) -> IO ()
    checkRes transition (name, locs, res) =
      case res of
        Sat model -> failMsg ("Array indices are not within bounds for " <> transition <> " " <> name <> ".")
          (prettyAnsi model) (printOutOfBounds model locs)
        Unsat -> pure ()
        Unknown -> errorMsg $ "Solver timeour. Cannot prove that array indices are within bounds for " <> transition <> " " <> name <> "."
        SMT.Error _ err -> errorMsg $ "Solver error: " <> err <> "\nCannot prove that array indices are within bounds for " <> transition <> " " <> name <> "."

    printOutOfBounds :: Model -> [Location] -> DocAnsi
    printOutOfBounds model locs =
      indent 2 ( underline (string "Out of bounds:"))
      <> line <> vsep printedLocs
      where
        printedLocs = runReader (mapM checkLocationBounds locs) model

    failMsg str model oobs = render (red (pretty str) <> line <> model <> line <> oobs <> line) >> exitFailure
    errorMsg str = render (pretty str <> line) >> exitFailure

checkBound :: TypedExp -> Int -> ModelCtx Bool
checkBound (TExp SInteger _ e) b =
  [ (0 <= toInteger idx) && (toInteger idx < toInteger b) | idx <- modelEval e ]
checkBound _ _ = error "Internal Error: Expected Integer indices"

checkRefBounds :: Ref a -> ModelCtx Bool
checkRefBounds (SArray _ ref _ idcs) = liftA2 (&&) (and <$> mapM (uncurry checkBound) idcs) (checkRefBounds ref)
checkRefBounds (SMapping _ ref _ _) = checkRefBounds ref
checkRefBounds (SField _ ref _ _) = checkRefBounds ref
checkRefBounds _ = pure True

checkLocationBounds :: Location -> ModelCtx DocAnsi
checkLocationBounds (Loc _ _ item@(Item _ _ ref)) = do
  cond <- checkRefBounds ref
  if cond then pure $ string ""
  else do
    i <- printOutOfBoundsItem item
    pure $ indent 4 $ string "Line " <> string (show l) <> string " Column " <> string (show c) <> string ": " <> i
  where
    (AlexPn _ l c) = posnFromRef ref

printIdx :: TypedExp -> Int -> ModelCtx DocAnsi
printIdx te@(TExp SInteger _ e) b = do
  idx <- modelEval e
  if (toInteger idx < toInteger b) && (0 <= toInteger idx)
    then pure $ string "[" <> string (prettyTypedExp te) <> string "]"
    else
      case e of
        LitInt _ _ -> pure $
          string "[" <> red (string (show idx))
          <> string " | " <>  green (string (show b)) <> string "]"
        _ -> pure $
          string "[(" <> string (prettyTypedExp te) <> string ") = " <> red (string ( show idx))
          <> string " | " <>  green (string (show b)) <> string "]"
printIdx _ _ = error "Internal Error: Expected Integer indices"

printOutOfBoundsRef :: Ref a -> ModelCtx DocAnsi
printOutOfBoundsRef (SArray _ ref _ idcs) =
  liftA2 (<>) (printOutOfBoundsRef ref) (concatWith (<>) <$> mapM (uncurry printIdx) idcs)
printOutOfBoundsRef (SMapping _ ref _ idcs) =
  liftA2 (<>) (printOutOfBoundsRef ref) (concatWith (<>)
    <$> mapM (\te -> pure $ string "[" <> string (prettyTypedExp te) <> string "]") idcs)
printOutOfBoundsRef (SField _ ref _ id') =
  liftA2 (<>) (printOutOfBoundsRef ref) (pure $ string $ "." ++ id')
printOutOfBoundsRef (SVar _ _ id') = pure $ string id'
printOutOfBoundsRef (CVar _ _ id') = pure $ string id'

printOutOfBoundsItem :: TItem a k-> ModelCtx DocAnsi
printOutOfBoundsItem (Item _ _ ref) = printOutOfBoundsRef ref


--- ** No rewrite aliasing ** ---

mkAliasingAssertion :: [Location] -> Exp ABoolean
mkAliasingAssertion ls = mkOr $ map (uncurry mkEqualityAssertion) $ combine ls

mkAliasingQuery :: Behaviour -> (Id, [[Location]], SMTExp, SolverInstance -> IO Model)
mkAliasingQuery behv@(Behaviour _ _ (Interface ifaceName decls) preconds caseconds _ stateUpdates _) =
  (ifaceName, groupedLocs, smt, getModel)
  where
    updatedLocs = locFromUpdate <$> stateUpdates
    updatedLocsIds = (\l@(Loc _ _ item) -> Arg (idsFromItem item) l) <$> updatedLocs
    groupedLocs = fmap (\(Arg _ b) -> b) <$> group (sort updatedLocsIds)

    activeLocs = nub $ concatMap (\(Loc _ rk item) -> locsFromItem rk item) updatedLocs
               <> concatMap locsFromExp preconds
               <> concatMap locsFromExp caseconds

    envs = ethEnvFromBehaviour behv

    assertLocGroupAliasings = mkAliasingAssertion <$> groupedLocs
    assertion = mkOr assertLocGroupAliasings

    (activeSLocs, activeCLocs) = partitionLocs activeLocs
    smt = mkDefaultSMT False activeSLocs activeCLocs envs ifaceName decls preconds caseconds [] assertion

    getModel solver = do
      prestate <- mapM (getLocationValue solver ifaceName Pre) activeSLocs
      calldata <- mapM (getCalldataValue solver ifaceName) decls
      calllocs <- mapM (getLocationValue solver ifaceName Pre) activeCLocs
      environment <- mapM (getEnvironmentValue solver) envs
      pure $ Model
        { _mprestate = prestate
        , _mpoststate = []
        , _mcalldata = (ifaceName, calldata)
        , _mcalllocs = calllocs
        , _menvironment = environment
        , _minitargs = []
        }

checkRewriteAliasing :: Act -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
checkRewriteAliasing (Act _ contracts)  solver' smttimeout debug =
  forM_ contracts (\(Contract _ behvs) -> do
    let config = SMT.SMTConfig solver' (fromMaybe 20000 smttimeout) debug
    solver <- spawnSolver config
    let behvQs = mkAliasingQuery <$> behvs
    r' <- forM behvQs (\(name, groupedLocs, q, getModel) -> do
                          res <- checkSat solver getModel q
                          pure (name, groupedLocs, res))
    mapM_ (checkRes "behaviour") r' )
  where
    checkRes :: String -> (Id, [[Location]], SMT.SMTResult) -> IO ()
    checkRes transition (name, locs, res) =
      case res of
        Sat model -> failMsg ("Rewrites are aliased for " <> transition <> " " <> name <> ".") (prettyAnsi model) (printLocs model locs)
        Unsat -> pure ()
        Unknown -> errorMsg $ "Solver timeour. Cannot prove that rewrites are not aliased for " <> transition <> " " <> name <> "."
        SMT.Error _ err -> errorMsg $ "Solver error: " <> err <> "\nSolver timeour. Cannot prove that rewrites are not aliased for"  <> transition <> " " <> name <> "."

    printLocs :: Model -> [[Location]] -> DocAnsi
    printLocs model locs =
      indent 2 $ underline (string "Rewrites:") <> line <> line <>
      vsep (runReader (mapM findAliased locs) model)

    failMsg str model rewrites = render (red (pretty str) <> line <> model <> line <> rewrites <> line) >> exitFailure
    errorMsg str = render (pretty str <> line) >> exitFailure


findAliased :: [Location] -> ModelCtx DocAnsi
findAliased locs =
  vsep <$> (mapM checkAliasing $ combine locs)

checkAliasing :: (Location, Location) -> ModelCtx DocAnsi
checkAliasing (l1, l2) = do
  isRewrite <- and <$> Control.Monad.zipWithM compareIdx ixs1 ixs2
  if isRewrite then
    liftA2 (<>) (indent 2 . vsep <$> sequence [printAliasedLoc l1, printAliasedLoc l2]) $ pure line
  else pure $ string ""
  where
    ixs1 = ixsFromLocation l1
    ixs2 = ixsFromLocation l2

compareIdx :: TypedExp -> TypedExp -> ModelCtx Bool
compareIdx (TExp SInteger Atomic e1) (TExp SInteger Atomic e2) =
  [ a == b | a <- modelEval e1, b <- modelEval e2 ]
compareIdx (TExp SBoolean Atomic e1) (TExp SBoolean Atomic e2) =
  [ a == b | a <- modelEval e1, b <- modelEval e2 ]
compareIdx (TExp SByteStr Atomic e1) (TExp SByteStr Atomic e2) =
  [ a == b | a <- modelEval e1, b <- modelEval e2 ]
compareIdx _ _ = pure False

printAliased :: TypedExp -> ModelCtx DocAnsi
printAliased te@(TExp SInteger _ e) = do
  e' <- modelEval e
  pure $ string "[(" <> string (prettyTypedExp te) <> string ") = " <> string (show e') <> string "]"
printAliased _ = error "Internal Error: Expected Integer indices"

printAliasedRef :: Ref a -> ModelCtx DocAnsi
printAliasedRef (SArray _ ref _ idcs) =
  liftA2 (<>) (printAliasedRef ref) (concatWith (<>) <$> mapM (printAliased . fst) idcs)
printAliasedRef (SMapping _ ref _ idcs) =
  liftA2 (<>) (printAliasedRef ref) (concatWith (<>) <$> mapM (\te -> pure $ string "[" <> string (prettyTypedExp te) <> string "]") idcs)
printAliasedRef (SField _ ref _ id') =
  liftA2 (<>) (printAliasedRef ref) (pure $ string id')
printAliasedRef (SVar _ _ id') = pure $ string id'
printAliasedRef (CVar _ _ id') = pure $ string id'

printAliasedLoc :: Location -> ModelCtx DocAnsi
printAliasedLoc (Loc _ _ (Item _ _ ref)) = do
  r <- printAliasedRef ref
  pure $ string "Line " <> string (show l) <> string " Column " <> string (show c) <> string ": " <> r
  where
    (AlexPn _ l c ) = posnFromRef ref

modelExpand :: SType (AArray a) -> Exp (AArray a) -> ModelCtx [Exp (Base (AArray a))]
modelExpand (SSArray SInteger) (Array _ l) = pure l
modelExpand (SSArray SBoolean) (Array _ l) = pure l
modelExpand (SSArray SByteStr) (Array _ l) = pure l
modelExpand (SSArray SContract) (Array _ l) = pure l
modelExpand (SSArray s@(SSArray _)) (Array _ l) = concat <$> mapM (modelExpand s) l
modelExpand typ (VarRef _ whn SStorage item) = do
  model <- ask
  case lookup (_Loc SStorage item) $ if whn == Pre then _mprestate model else _mpoststate model of
    Just (TExp sType _ e') -> case testEquality typ sType of
      Just Refl -> pure $ expandArrayExpr sType e'
      _ -> error "modelEval: Storage Location given does not match type"
    _ -> error $ "modelEval: Storage Location not found in model" <> show item
modelExpand typ (VarRef _ _ SCalldata item) = do
  model <- ask
  case lookup (_Loc SCalldata item) $ _mcalllocs model of
    Just (TExp sType _ e') -> case testEquality typ sType of
      Just Refl -> pure $ expandArrayExpr sType e'
      _ -> error "modelEval: Storage Location given does not match type"
    _ -> error $ "modelEval: Storage Location not found in model" <> show item
modelExpand typ (ITE pn tbool e1 e2) = do
  e1' <- modelExpand typ e1
  e2' <- modelExpand typ e2
  pure $ (uncurry $ ITE pn tbool) <$> zip e1' e2'

modelEval :: forall (a :: ActType). SingI a => Exp a -> ModelCtx (TypeOf a)
modelEval e = case e of
  And  _ a b    -> [ a' && b' | a' <- modelEval a, b' <- modelEval b]
  Or   _ a b    -> [ a' || b' | a' <- modelEval a, b' <- modelEval b]
  Impl _ a b    -> [ a' <= b' | a' <- modelEval a, b' <- modelEval b]
  Neg  _ a      -> not <$> modelEval a
  LT   _ a b    -> [ a' <  b' | a' <- modelEval a, b' <- modelEval b]
  LEQ  _ a b    -> [ a' <= b' | a' <- modelEval a, b' <- modelEval b]
  GT   _ a b    -> [ a' >  b' | a' <- modelEval a, b' <- modelEval b]
  GEQ  _ a b    -> [ a' >= b' | a' <- modelEval a, b' <- modelEval b]
  LitBool _ a   -> pure a

  Add _ a b     -> [ a' + b'     | a' <- modelEval a, b' <- modelEval b]
  Sub _ a b     -> [ a' - b'     | a' <- modelEval a, b' <- modelEval b]
  Mul _ a b     -> [ a' * b'     | a' <- modelEval a, b' <- modelEval b]
  Div _ a b     -> [ a' `div` b' | a' <- modelEval a, b' <- modelEval b]
  Mod _ a b     -> [ a' `mod` b' | a' <- modelEval a, b' <- modelEval b]
  Exp _ a b     -> [ a' ^ b'     | a' <- modelEval a, b' <- modelEval b]
  LitInt  _ a   -> pure a
  IntMin  _ a   -> pure $ intmin  a
  IntMax  _ a   -> pure $ intmax  a
  UIntMin _ a   -> pure $ uintmin a
  UIntMax _ a   -> pure $ uintmax a

  Eq _ SInteger x y -> [ x' == y' | x' <- modelEval x, y' <- modelEval y]
  Eq _ SBoolean x y -> [ x' == y' | x' <- modelEval x, y' <- modelEval y]
  Eq _ SByteStr x y -> [ x' == y' | x' <- modelEval x, y' <- modelEval y]
  Eq p s@(SSArray _) a b -> do
    a' <- modelExpand s a
    b' <- modelExpand s b
    let s' = flattenSType s
        eqs = (uncurry $ Eq p s') <$> zip a' b'
        expanded = foldr (And nowhere) (LitBool nowhere True) eqs
    modelEval expanded
  NEq _ SInteger x y -> [ x' /= y' | x' <- modelEval x, y' <- modelEval y]
  NEq _ SBoolean x y -> [ x' /= y' | x' <- modelEval x, y' <- modelEval y]
  NEq _ SByteStr x y -> [ x' /= y' | x' <- modelEval x, y' <- modelEval y]
  NEq p s@(SSArray _) a b -> do
    a' <- modelExpand s a
    b' <- modelExpand s b
    let s' = flattenSType s
        eqs = (uncurry $ NEq p s') <$> zip a' b'
        expanded = foldr (Or nowhere) (LitBool nowhere False) eqs
    modelEval expanded

  ITE _ a b c   ->  modelEval a >>= \cond -> if cond then modelEval b else modelEval c

  Array _ l -> case (sing @a) of
    SSArray SType -> mapM modelEval l

  Create _ _ _ -> error "modelEval of contracts not supported"
  VarRef _ whn SStorage item -> do
    model <- ask
    case lookup (_Loc SStorage item) $ if whn == Pre then _mprestate model else _mpoststate model of
      Just (TExp sType _ e') -> case testEquality (sing @a) sType of
        Just Refl -> case e' of
          (LitInt _ i) -> pure i
          (LitBool _ b) -> pure b
          (ByLit _ s) -> pure s
          (Array _ _) -> pure $ fromMaybe (error "modelEval: expected array literal") $ eval e'
          _ -> error "modelEval: Model did not return a literal"
        _ -> error "modelEval: Storage Location given does not match type"
      _ -> error $ "modelEval: Storage Location not found in model" <> show item
  VarRef _ _ SCalldata item -> do
    model <- ask
    case lookup (_Loc SCalldata item) $ _mcalllocs model of
      Just (TExp sType _ e') -> case testEquality (sing @a) sType of
        Just Refl -> case e' of
          (LitInt _ i) -> pure i
          (LitBool _ b) -> pure b
          (ByLit _ s) -> pure s
          (Array _ _) -> pure $ fromMaybe (error "modelEval: expected array literal") $ eval e'
          _ -> error "modelEval: Model did not return a literal"
        _ -> error "modelEval: Calldata Location given does not match type"
      _ -> error "modelEval: Calldata Location not found in model"

  IntEnv _ env     -> do
    model <- ask
    case lookup env $ _menvironment model of
      Just (TExp sType _ e') -> case testEquality (sing @a) sType of
        Just Refl -> case e' of
          (LitInt _ i) -> pure i
          _ -> error "modelEval: Model did not return an Integer literal"
        _ -> error "modelEval: Environmental variable given does not match type"
      _ -> error "modelEval: Enviromental variable not found in model"
  _ -> error "modelEval: TODO"
