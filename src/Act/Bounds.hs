{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Act.Bounds (addBounds, mkRefsBounds) where

import Data.Maybe
import Data.List (nub)
import Data.Type.Equality

import Act.Syntax
import Act.Syntax.TypedExplicit


{-|

Module      : Bounds
Description : This pass adds integer add integer type bounds as preconditions
and postconditions.
-}

-- | Adds preconditions and postconditions to constructors and behaviors that
-- ensure that integer calldata and storage variables are within the range
-- specified by their types.
addBounds :: Act -> Act
addBounds (Act store contracts) = Act store (addBoundsContract <$> contracts)
  where
    addBoundsContract (Contract ctors behvs) = Contract (addBoundsConstructor ctors) (addBoundsBehaviour <$> behvs)

-- | Adds type bounds for calldata, environment vars, and external storage vars
-- as preconditions
addBoundsConstructor :: Constructor -> Constructor
addBoundsConstructor ctor@(Constructor _ (Interface _ decls) _ pre cases _ invs) =
  ctor { _cpreconditions = pre'
       , _invariants = invs' }
    where
      pre' = nub $ pre
             <> mkCallDataBounds decls
             <> mkEthEnvBounds (ethEnvFromConstructor ctor)
              -- The following is sound as values of locations outside local storage
              -- already exist as the constructor starts executing,
              -- and the constructor cannot modify non-local locations.
             <> mkRefsBounds locs
      invs' = addBoundsInvariant ctor <$> invs

      locs = nub $ concatMap locsFromExp pre
             <> concatMap locsFromInvariant invs
             <> concatMap locsFromConstrCase cases


-- | Adds type bounds for calldata, environment vars, and storage vars as preconditions
addBoundsBehaviour :: Behaviour -> Behaviour
addBoundsBehaviour behv@(Behaviour _ _ (Interface _ decls) _ pre cases _) =
  behv { _preconditions = pre' }
    where
      pre' = nub $ pre
             <> mkCallDataBounds decls
             <> mkRefsBounds locs
             <> mkEthEnvBounds (ethEnvFromBehaviour behv)

      locs = nub $ concatMap locsFromExp pre
             <> concatMap locsFromCase cases

-- | Adds type bounds for calldata, environment vars, and storage vars
addBoundsInvariant :: Constructor -> Invariant -> Invariant
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

mkEthEnvBounds :: [EthEnv] -> [Exp ABoolean]
mkEthEnvBounds vars = catMaybes $ mkBound <$> nub vars
  where
    mkBound :: EthEnv -> Maybe (Exp ABoolean)
    mkBound e = Just $ bound (ethEnv e) (IntEnv nowhere e)

isBoundedIntegerType :: TValueType a -> Maybe (a :~: AInteger)
isBoundedIntegerType TUnboundedInt = Nothing
isBoundedIntegerType t = testEquality (toSType t) SInteger

refToRHS :: Ref k -> Ref RHS
refToRHS (SVar p t i ci) = SVar p t i ci
refToRHS (CVar p t i) = CVar p t i
refToRHS (RMapIdx p r i) = RMapIdx p r i
refToRHS (RArrIdx p r i n) = RArrIdx p (refToRHS r) i n
refToRHS (RField p r i n) = RField p (refToRHS r) i n

mkRefsBounds :: [TypedRef] -> [Exp ABoolean]
mkRefsBounds refs = concatMap mkTRefBound refs
  where
    mkTRefBound :: TypedRef -> [Exp ABoolean]
    mkTRefBound (TRef t@(TInteger _ _) _ ref) = [mkRefBound t ref]
    mkTRefBound (TRef t@TAddress _ ref) = [mkRefBound t ref]
    mkTRefBound (TRef t@(TArray _ _) _ ref) =
      let bt = fst (flattenValueType t) in
      case isBoundedIntegerType bt of
        Just Refl -> mkRefBound bt <$> expandTRef t ref
        Nothing -> []
    mkTRefBound _ = []

    mkRefBound :: TValueType AInteger -> Ref k -> Exp ABoolean
    mkRefBound t ref = bound t (VarRef nowhere t (refToRHS ref))


mkCallDataBounds :: [Arg] -> [Exp ABoolean]
mkCallDataBounds = concatMap $ \(Arg argtyp name) -> case argtyp of
  (AbiArg typ) -> case typ of
      -- Array element bounds are applied lazily when needed in mkCalldataLocationBounds
    (AbiArrayType _ _) -> []
    _ -> case fromAbiType typ of
         ValueType t@(TInteger _ _) -> [bound t (_Var t name)]
         ValueType TAddress -> [bound TAddress (_Var TAddress name)]
         _ -> []
  (ContractArg _ cid) -> [bound TAddress (Address nowhere cid (_Var (TContract cid) name))]
