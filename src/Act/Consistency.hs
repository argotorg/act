{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE DataKinds #-}
{-# Language ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TupleSections #-}

module Act.Consistency (
  --checkArrayBounds,
  checkUpdateAliasing
) where


import Prelude hiding (GT, LT)

import Data.List
import Prettyprinter hiding (group)
import System.Exit (exitFailure)
import Data.Maybe
import Data.Type.Equality ((:~:)(..), TestEquality (testEquality))
import Data.Singletons (sing, SingI)
import qualified Data.Bifunctor as Bif
import qualified Data.Semigroup as Semi (Arg (..))

import Control.Monad.Reader
import Control.Monad (forM, forM_, zipWithM)

import Act.Lex (AlexPosn(..))
import Act.Syntax
import Act.Syntax.TypedExplicit
import Act.SMT as SMT
import Act.Bounds
import Act.Print

import qualified EVM.Solvers as Solvers

--- ** Array Bounds Checking ** ---
{-

mkBounds :: TypedExp -> Int -> [Exp ABoolean]
mkBounds (TExp (TInteger _ _) e) b = [LEQ nowhere (LitInt nowhere 0) e, LT nowhere e (LitInt nowhere $ toInteger b)]
mkBounds _ _ = error "Internal Error: Expected Integral Index"

mkRefBounds :: Ref a -> [Exp ABoolean]
mkRefBounds (RArrIdx _ ref _ tes) = concatMap (uncurry mkBounds) tes <> mkRefBounds ref
mkRefBounds (RMapIdx _ ref _) = mkRefBounds ref
mkRefBounds (RField _ ref _ _) = mkRefBounds ref
mkRefBounds _ = []

mkStorageBounds :: TypedRef -> [Exp ABoolean]
mkStorageBounds (TRef _ _ ref) = mkRefBounds ref

-- TODO: There are locs that don't need to be checked, e.g. assignment locs cannot be out of bounds
mkConstrArrayBoundsQuery :: Constructor -> (Id, [TypedRef], SMTExp, SolverInstance -> IO Model)
mkConstrArrayBoundsQuery constructor@(Constructor _ (Interface ifaceName decls) _ preconds cases _ _) =
  (ifaceName, arrayLocs, smt, getModel)
  where
    -- Declare vars
    activeLocs = locsFromConstructor constructor
    envs = ethEnvFromConstructor constructor

    arrayLocs = filter (\(TRef _ _ ref) -> isArrayRef ref && posnFromItem ref /= nowhere) activeLocs
    boundsExps = concatMap mkStorageBounds arrayLocs
    assertion = mkOrNot boundsExps

    (activeSLocs, activeCLocs) = partitionLocs activeLocs
    smt = mkDefaultSMT True activeSLocs activeCLocs envs ifaceName decls preconds [] initialStorage assertion

    getModel = getCtorModel constructor

mkBehvArrayBoundsQuery :: Behaviour -> (Id, [TypedRef], SMTExp, SolverInstance -> IO Model)
mkBehvArrayBoundsQuery behv@(Behaviour _ _ (Interface ifaceName decls) preconds cases _ _) =
  (ifaceName, arrayLocs, smt, getModel)
  where
    -- Declare vars
    activeLocs = locsFromBehaviour behv
    envs = ethEnvFromBehaviour behv

    arrayLocs = filter (\(TRef _ _ ref) -> isArrayItem ref && posnFromItem ref /= nowhere) activeLocs
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
    checkRes :: String -> (Id, [TypedRef], SMT.SMTResult) -> IO ()
    checkRes transition (name, locs, res) =
      case res of
        Sat model -> failMsg ("Array indices are not within bounds for " <> transition <> " " <> name <> ".")
          (prettyAnsi model) (printOutOfBounds model locs)
        Unsat -> pure ()
        Unknown -> errorMsg $ "Solver timeour. Cannot prove that array indices are within bounds for " <> transition <> " " <> name <> "."
        SMT.Error _ err -> errorMsg $ "Solver error: " <> err <> "\nCannot prove that array indices are within bounds for " <> transition <> " " <> name <> "."

    printOutOfBounds :: Model -> [TypedRef] -> DocAnsi
    printOutOfBounds model locs =
      indent 2 ( underline (string "Out of bounds:"))
      <> line <> vsep printedLocs
      where
        printedLocs = runReader (mapM checkLocationBounds locs) model

    failMsg str model oobs = render (red (pretty str) <> line <> model <> line <> oobs <> line) >> exitFailure
    errorMsg str = render (pretty str <> line) >> exitFailure

checkBound :: TypedExp -> Int -> ModelCtx Bool
checkBound (TExp (TInteger _ _) e) b =
  [ (0 <= toInteger idx) && (toInteger idx < toInteger b) | idx <- modelEval e ]
checkBound _ _ = error "Internal Error: Expected Integer indices"

checkRefBounds :: Ref a -> ModelCtx Bool
checkRefBounds (RArrIdx _ ref _ idcs) = liftA2 (&&) (and <$> mapM (uncurry checkBound) idcs) (checkRefBounds ref)
checkRefBounds (RMapIdx _ ref _) = checkRefBounds ref
checkRefBounds (RField _ ref _ _) = checkRefBounds ref
checkRefBounds _ = pure True

checkLocationBounds :: TypedRef -> ModelCtx DocAnsi
checkLocationBounds (TRef _ _ ref) = do
  cond <- checkRefBounds ref
  if cond then pure $ string ""
  else do
    i <- printOutOfBoundsItem item
    pure $ indent 4 $ string "Line " <> string (show l) <> string " Column " <> string (show c) <> string ": " <> i
  where
    (AlexPn _ l c) = posnFromRef ref

printIdx :: TypedExp -> Int -> ModelCtx DocAnsi
printIdx te@(TExp (TInteger _ _) e) b = do
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
printOutOfBoundsRef (RArrIdx _ ref _ idcs) =
  liftA2 (<>) (printOutOfBoundsRef ref) (concatWith (<>) <$> mapM (uncurry printIdx) idcs)
printOutOfBoundsRef (RMapIdx _ ref idcs) =
  liftA2 (<>) (printOutOfBoundsRef ref) (concatWith (<>)
    <$> mapM (\te -> pure $ string "[" <> string (prettyTypedExp te) <> string "]") idcs)
printOutOfBoundsRef (RField _ ref _ id') =
  liftA2 (<>) (printOutOfBoundsRef ref) (pure $ string $ "." ++ id')
printOutOfBoundsRef (SVar _ _ _ id') = pure $ string id'
printOutOfBoundsRef (CVar _ _ id') = pure $ string id'

printOutOfBoundsItem :: TypedRef -> ModelCtx DocAnsi
printOutOfBoundsItem (TRef _ _ ref) = printOutOfBoundsRef ref
  -}


type ModelCtx = Reader Model

--- ** No rewrite aliasing ** ---

combine :: [a] -> [(a,a)]
combine lst = combine' lst []
  where
    combine' [] acc = concat acc
    combine' (x:xs) acc =
      let xcomb = [ (x, y) | y <- xs] in
      combine' xs (xcomb:acc)

-- | Decompose a reference to a list of ll identifiers,
-- and a list of all index expressions present in it.
decompLRef :: Ref LHS -> ([Id], [TypedExp])
decompLRef ref = go ref [] []
  where
  go :: Ref LHS -> [Id] -> [TypedExp] -> ([Id], [TypedExp])
  go (SVar _ _ _ name) ids ixs = (name : ids, ixs)
  go (RArrIdx _ r ix _) ids ixs = go r ids ((TExp (TInteger 256 Unsigned) ix) : ixs)
  go (RField _ r _ name) ids ixs = go r (name : ids) ixs

-- | If the two references may be aliased for some model, then return the expressions
-- that must be satisfied in order for aliasing to happen.
-- If the returned list is empty then the references are identical.
-- If the two references refer to different base slots then return `Nothing`.
aliasingCondition :: StorageUpdate -> StorageUpdate -> Maybe [Exp ABoolean]
aliasingCondition (Update _ r1 _) (Update _ r2 _) = if ids1 == ids2 then zipWithM andIxs ixs1 ixs2 else Nothing
  where
  (ids1, ixs1) = decompLRef r1
  (ids2, ixs2) = decompLRef r2

  andIxs :: TypedExp -> TypedExp -> Maybe (Exp ABoolean)
  andIxs (TExp t1 e1) (TExp t2 e2) = (\Refl -> Just (Eq nowhere t1 e1 e2)) =<< testEquality t1 t2

aliasingCandidates :: [StorageUpdate] -> [((StorageUpdate, StorageUpdate), [Exp ABoolean])]
aliasingCandidates upds = mapMaybe (\p -> (p,) <$> uncurry aliasingCondition p) $ combine upds

checkCaseUpdateAliasing :: Id -> [Arg] -> [Exp ABoolean] -> Bcase -> (Id, [(StorageUpdate, StorageUpdate)], SMTExp, SolverInstance -> IO Model)
checkCaseUpdateAliasing bname decls preconds (Case _ casecond (upds, _)) =
  (bname, fst <$> maybeAliasedPairs, mkDefaultSMT activeRefs envs bname decls preconds integerBounds assertion, getModel)
  where
    maybeAliasedPairs = aliasingCandidates upds
    activeRefs = concat (concatMap (fmap locsFromExp . snd) maybeAliasedPairs)
              <> concatMap locsFromExp preconds <> locsFromExp casecond
    envs = concat $ concatMap (fmap ethEnvFromExp . snd) maybeAliasedPairs
        <> map ethEnvFromExp preconds <> pure (ethEnvFromExp casecond)

    integerBounds = mkRefsBounds activeRefs <> mkEthEnvBounds envs

    pairAliasingAssertion = foldr (And nowhere) (LitBool nowhere True)
    assertion = foldr (Or nowhere . pairAliasingAssertion . snd) (LitBool nowhere False) maybeAliasedPairs

    getModel solver = do
      prestate <- mapM (getLocationValue solver bname Pre) activeRefs
      calldata <- mapM (getCalldataValue solver bname) decls
      calllocs <- mapM (getLocationValue solver bname Pre) activeRefs
      environment <- mapM (getEnvironmentValue solver) envs
      pure $ Model
        { _mprestate = prestate
        , _mpoststate = []
        , _mcalldata = (bname, calldata)
        , _mcalllocs = calllocs
        , _menvironment = environment
        , _minitargs = []
        }


checkBehvUpdateAliasing :: Behaviour -> [(Id, [(StorageUpdate, StorageUpdate)], SMTExp, SolverInstance -> IO Model)]
checkBehvUpdateAliasing (Behaviour bname _ (Interface _ decls) _ preconds cases _) =
  checkCaseUpdateAliasing bname decls preconds <$> cases


checkUpdateAliasing :: Act -> Solvers.Solver -> Maybe Integer -> Bool -> IO ()
checkUpdateAliasing (Act _ contracts)  solver' smttimeout debug =
  forM_ contracts (\(Contract _ behvs) -> do
    let config = SMT.SMTConfig solver' (fromMaybe 20000 smttimeout) debug
    solver <- spawnSolver config
    let behvQs = concatMap checkBehvUpdateAliasing behvs
    r' <- forM behvQs (\(name, updPairs, q, getModel) -> do
                          res <- checkSat solver getModel q
                          pure (name, updPairs, res))
    mapM_ (checkRes "behaviour") r' )
  where
    checkRes :: String -> (Id, [(StorageUpdate, StorageUpdate)], SMT.SMTResult) -> IO ()
    checkRes transition (name, locs, res) =
      case res of
        Sat model -> failMsg ("Updates are aliased for " <> transition <> " " <> name <> ".") (prettyAnsi model) (printLocs model locs)
        Unsat -> pure ()
        Unknown -> errorMsg $ "Solver timeour. Cannot prove that updates are not aliased for " <> transition <> " " <> name <> "."
        SMT.Error _ err -> errorMsg $ "Solver error: " <> err <> "\nSolver timeour. Cannot prove that updates are not aliased for "  <> transition <> " " <> name <> "."

    printLocs :: Model -> [(StorageUpdate, StorageUpdate)] -> DocAnsi
    printLocs model locs =
      indent 2 $ underline (string "Updates:") <> line <> line <>
      vsep (catMaybes (runReader (mapM checkAliasing locs) model))

    failMsg str model rewrites = render (red (pretty str) <> line <> model <> line <> rewrites <> line) >> exitFailure
    errorMsg str = render (pretty str <> line) >> exitFailure


checkAliasing :: (StorageUpdate, StorageUpdate) -> ModelCtx (Maybe DocAnsi)
checkAliasing ((Update _ r1 _), (Update _ r2 _)) = do
  isRewrite <- and <$> zipWithM compareIdx ixs1 ixs2
  if isRewrite then
    liftA2 (<>) (Just . indent 2 . vsep <$> sequence [printAliasedLoc r1, printAliasedLoc r2]) $ pure (Just line)
  else pure Nothing
  where
    ixs1 = ixsFromRef r1
    ixs2 = ixsFromRef r2

compareIdx :: TypedExp -> TypedExp -> ModelCtx Bool
compareIdx (TExp (TInteger _ _) e1) (TExp (TInteger _ _) e2) =
  [ a == b | a <- modelEval e1, b <- modelEval e2 ]
compareIdx (TExp TBoolean e1) (TExp TBoolean e2) =
  [ a == b | a <- modelEval e1, b <- modelEval e2 ]
compareIdx (TExp TByteStr e1) (TExp TByteStr e2) =
  [ a == b | a <- modelEval e1, b <- modelEval e2 ]
compareIdx _ _ = pure False

printAliased :: TypedExp -> ModelCtx DocAnsi
printAliased te@(TExp (TInteger _ _) e) = do
  e' <- modelEval e
  pure $ string "[(" <> string (prettyTypedExp te) <> string ") = " <> string (show e') <> string "]"
printAliased _ = error "Internal Error: Expected Integer indices"

printAliasedRef :: Ref k -> ModelCtx DocAnsi
printAliasedRef (RArrIdx _ ref idx _) =
  liftA2 (<>) (printAliasedRef ref) (printAliased (TExp (TInteger 256 Unsigned) idx))
printAliasedRef (RMapIdx _ (TRef _ _ ref) idx) = do
  pr <- printAliasedRef ref
  pix <- printAliased idx
  pure $ pr <> (string "[") <> pix <> (string "]")
printAliasedRef (RField _ ref _ id') =
  liftA2 (<>) (printAliasedRef ref) (pure $ string id')
printAliasedRef (SVar _ _ _ id') = pure $ string id'
printAliasedRef (CVar _ _ id') = pure $ string id'

printAliasedLoc :: Ref k -> ModelCtx DocAnsi
printAliasedLoc ref = do
  r <- printAliasedRef ref
  pure $ string "Line " <> string (show l) <> string " Column " <> string (show c) <> string ": " <> r
  where
    (AlexPn _ l c ) = posnFromRef ref

modelExpand :: TValueType (AArray a) -> Exp (AArray a) -> ModelCtx [Exp (Base (AArray a))]
modelExpand (TArray _ (TInteger _ _)) (Array _ l) = pure l
modelExpand (TArray _ TUnboundedInt) (Array _ l) = pure l
modelExpand (TArray _ TAddress) (Array _ l) = pure l
modelExpand (TArray _ TBoolean) (Array _ l) = pure l
modelExpand (TArray _ TByteStr) (Array _ l) = pure l
modelExpand (TArray _ (TContract _)) (Array _ l) = pure l
modelExpand (TArray _ (TStruct _)) (Array _ l) = pure l
modelExpand (TArray _ (TMapping _ _)) (Array _ l) = pure l
modelExpand (TArray _ t@(TArray _ _)) (Array _ l) = concat <$> mapM (modelExpand t) l
modelExpand typ (VarRef _ t ref) = do
  model <- ask
  case lookup (TRef t SRHS ref) (_mprestate model) of
    Just (TExp sType e') -> case testEquality typ sType of
      Just Refl -> pure $ expandArrayExpr sType e'
      _ -> error "modelEval: Storage Location given does not match type"
    _ -> error $ "modelEval: Storage Location not found in model" <> show ref
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

  Eq _ (TInteger _ _) x y -> [ x' == y' | x' <- modelEval x, y' <- modelEval y]
  Eq _ TAddress x y -> [ x' == y' | x' <- modelEval x, y' <- modelEval y]
  Eq _ TBoolean x y -> [ x' == y' | x' <- modelEval x, y' <- modelEval y]
  Eq _ TByteStr x y -> [ x' == y' | x' <- modelEval x, y' <- modelEval y]
  Eq _ (TStruct _) _ _ -> error "modelEval: TODO: Structs"
  Eq _ (TContract _) _ _ -> error "modelEval: TODO: Structs"
  Eq p s@(TArray _ _) a b -> do
    a' <- modelExpand s a
    b' <- modelExpand s b
    let s' = fst $ flattenValueType s
        eqs = (uncurry $ Eq p s') <$> zip a' b'
        expanded = foldr (And nowhere) (LitBool nowhere True) eqs
    modelEval expanded

  NEq _ (TInteger _ _) x y -> [ x' /= y' | x' <- modelEval x, y' <- modelEval y]
  NEq _ TAddress x y -> [ x' /= y' | x' <- modelEval x, y' <- modelEval y]
  NEq _ TBoolean x y -> [ x' /= y' | x' <- modelEval x, y' <- modelEval y]
  NEq _ TByteStr x y -> [ x' /= y' | x' <- modelEval x, y' <- modelEval y]
  NEq _ (TStruct _) _ _ -> error "modelEval: TODO: Structs"
  NEq _ (TContract _) _ _ -> error "modelEval: TODO: Structs"
  NEq p s@(TArray _ _) a b -> do
    a' <- modelExpand s a
    b' <- modelExpand s b
    let s' = fst $ flattenValueType s
        eqs = (uncurry $ NEq p s') <$> zip a' b'
        expanded = foldr (Or nowhere) (LitBool nowhere False) eqs
    modelEval expanded

  ITE _ a b c   ->  modelEval a >>= \cond -> if cond then modelEval b else modelEval c

  Array _ l -> case (sing @a) of
    SSArray SType -> mapM modelEval l

  Create _ _ _ _ -> error "modelEval of contracts not supported"
  VarRef _ vt ref -> do
    model <- ask
    case lookup (TRef vt SRHS ref) (_mprestate model) of
      Just (TExp vType e') -> case testEquality vt vType of
        Just Refl -> case e' of
          (LitInt _ i) -> pure i
          (LitBool _ b) -> pure b
          (ByLit _ s) -> pure s
          (Array _ _) -> pure $ fromMaybe (error "modelEval: expected array literal") $ eval e'
          _ -> error "modelEval: Model did not return a literal"
        _ -> error "modelEval: Storage Location given does not match type"
      _ -> error $ "modelEval: Storage Location not found in model" <> show ref

  IntEnv _ env     -> do
    model <- ask
    case lookup env $ _menvironment model of
      Just (TExp sType e') -> case testEquality (sing @a) (toSType sType) of
        Just Refl -> case e' of
          (LitInt _ i) -> pure i
          _ -> error "modelEval: Model did not return an Integer literal"
        _ -> error "modelEval: Environmental variable given does not match type"
      _ -> error "modelEval: Enviromental variable not found in model"
  _ -> error "modelEval: TODO"
