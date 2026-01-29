{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Act.Bounds (addBounds, addBoundsConstructor, boundsConstructor, addBoundsBehaviour, boundsBehaviour, mkRefsBounds, mkEthEnvBounds, mkCallDataBounds) where

import Data.Maybe
import Data.List (nub)
import Data.Type.Equality

import Act.Syntax
import Act.Syntax.Typed


{-|

Module      : Bounds
Description : This pass adds integer type bounds as preconditions.
-}

-- | Adds preconditions and postconditions to constructors and behaviors that
-- ensure that integer calldata and storage variables are within the range
-- specified by their types.
addBounds :: Act t -> Act t
addBounds (Act store contracts) = Act store (addBoundsContract <$> contracts)
  where
    addBoundsContract (Contract src ctors behvs) = Contract src (addBoundsConstructor ctors) (addBoundsBehaviour <$> behvs)

-- | Adds type bounds for calldata, environment vars, and external storage vars
-- as preconditions
addBoundsConstructor :: Constructor t -> Constructor t
addBoundsConstructor ctor@(Constructor _ (Interface _ decls) _ pre cases _ invs) =
  ctor { _cpreconditions = pre'
       , _invariants = addBoundsInvariant ctor <$> invs }
    where
      pre' = pre <> boundsConstructor ctor

boundsConstructor :: Constructor t -> [Exp ABoolean t]
boundsConstructor ctor@(Constructor _ (Interface _ decls) _ pre cases _ invs) = pre'
    where
      pre' = nub $ mkCallDataBounds decls
             <> mkEthEnvBounds (ethEnvFromConstructor ctor)
              -- The following is sound as values of locations outside local storage
              -- already exist as the constructor starts executing,
              -- and the constructor cannot modify non-local locations.
             <> mkRefsBounds locs

      locs = nub $ concatMap locsFromExp pre
             <> concatMap locsFromInvariant invs
             <> concatMap locsFromConstrCase cases

-- | Adds type bounds for calldata, environment vars, and storage vars as preconditions
addBoundsBehaviour :: Behaviour t -> Behaviour t
addBoundsBehaviour behv@(Behaviour _ _ (Interface _ decls) _ pre cases _) =
  behv { _preconditions = pre' }
    where
      pre' = pre <> boundsBehaviour behv

boundsBehaviour :: Behaviour t -> [Exp ABoolean t]
boundsBehaviour behv@(Behaviour _ _ (Interface _ decls) _ pre cases _) = pre'
    where
      pre' = nub $ mkCallDataBounds decls
             <> mkRefsBounds locs
             <> mkEthEnvBounds (ethEnvFromBehaviour behv)

      locs = nub $ concatMap locsFromExp pre
             <> concatMap locsFromCase cases

-- | Adds type bounds for calldata, environment vars, and storage vars
addBoundsInvariant :: Constructor t -> Invariant t -> Invariant t
addBoundsInvariant (Constructor _ (Interface _ decls) _ _ _ _ _) inv@(Invariant _ preconds storagebounds (PredTimed predicate _)) =
  inv { _ipreconditions = preconds', _istoragebounds = storagebounds' }
    where
      preconds' = nub $ preconds
                  <> mkCallDataBounds decls
                  <> mkEthEnvBounds (ethEnvFromExp predicate)
                  <> mkRefsBounds locs
      storagebounds' = storagebounds
                       <> mkRefsBounds locs

      locs = nub $ concatMap locsFromExp (preconds <> storagebounds)
             <> locsFromExp predicate
      --(nonlocalLocs, localLocs) = partition (not . isLocalLoc) locs
addBoundsInvariant (Constructor _ (Interface _ decls) _ _ _ _ _) inv@(Invariant _ preconds storagebounds (PredUntimed predicate)) =
  inv { _ipreconditions = preconds', _istoragebounds = storagebounds' }
    where
      preconds' = nub $ preconds
                  <> mkCallDataBounds decls
                  <> mkEthEnvBounds (ethEnvFromExp predicate)
                  <> mkRefsBounds locs
      storagebounds' = storagebounds
                       <> mkRefsBounds locs

      locs = nub $ concatMap locsFromExp (preconds <> storagebounds)
             <> locsFromExp predicate

mkEthEnvBounds :: [EthEnv] -> [Exp ABoolean t]
mkEthEnvBounds = mapMaybe mkBound . nub
  where
    mkBound :: EthEnv -> Maybe (Exp ABoolean t)
    mkBound e = Just $ bound (ethEnv e) (IntEnv nowhere e)

isBoundedIntegerType :: TValueType a -> Maybe (a :~: AInteger)
isBoundedIntegerType TUnboundedInt = Nothing
isBoundedIntegerType t = testEquality (toSType t) SInteger

mkRefsBounds :: [TypedRef t] -> [Exp ABoolean t]
mkRefsBounds refs = concatMap mkTRefBound refs
  where
    mkTRefBound :: TypedRef t -> [Exp ABoolean t]
    mkTRefBound (TRef t@(TInteger _ _) _ ref) = [mkRefBound t ref]
    mkTRefBound (TRef t@TAddress _ ref) = [mkRefBound t ref]
    mkTRefBound (TRef t@(TArray _ _) _ ref) =
      let bt = fst (flattenValueType t) in
      case isBoundedIntegerType bt of
        Just Refl -> mkRefBound bt <$> expandTRef t ref
        Nothing -> []
    mkTRefBound _ = []

    mkRefBound :: TValueType AInteger -> Ref k t -> Exp ABoolean t
    mkRefBound t ref = bound t (VarRef nowhere t (refToRHS ref))


mkCallDataBounds :: [Arg] -> [Exp ABoolean t]
mkCallDataBounds = concatMap $ \(Arg argtyp name) -> case argtyp of
  (AbiArg typ) -> case typ of
      -- Array element bounds are applied lazily when needed in mkCalldataLocationBounds
    (AbiArrayType _ _) -> []
    _ -> case fromAbiType typ of
         ValueType t@(TInteger _ _) -> [bound t (_Var t name)]
         ValueType TAddress -> [bound TAddress (_Var TAddress name)]
         _ -> []
  (ContractArg _ _) -> []
  -- there is no need to bound addresses range of contracts since it may never go out of bounds by construction
  -- [bound TAddress (Address nowhere cid (_Var (TContract cid) name))]
