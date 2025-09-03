{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ViewPatterns #-}

module Act.Bounds (addBounds) where

import Data.Maybe
import Data.List (nub, (\\), partition)
import Data.List.NonEmpty (toList)
import Data.Type.Equality

import Act.Syntax
import Act.Syntax.TypedExplicit
import Act.Type (globalEnv)
import Debug.Trace


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
addBoundsConstructor ctor@(Constructor _ (Interface _ decls) _ pre post invs stateUpdates) =
  ctor { _cpreconditions = pre'
       , _cpostconditions = post'
       , _invariants = invs' }
    where
      pre' = pre
             <> mkCallDataBounds decls
             <> mkCalldataLocationBounds clocs
             <> mkEthEnvBounds (ethEnvFromConstructor ctor)
             <> mkStorageBoundsLoc externalSLocs
      invs' = addBoundsInvariant ctor <$> invs
      post' = post <> mkStorageBounds stateUpdates Post

      locs = concatMap locsFromExp (pre <> post)
            <> concatMap locsFromInvariant invs
            <> concatMap locsFromUpdate stateUpdates
      (slocs, clocs) = partitionLocs locs
      (_, externalSLocs) = partition isLocalLoc slocs

-- | Adds type bounds for calldata, environment vars, and storage vars as preconditions
addBoundsBehaviour :: Behaviour -> Behaviour
addBoundsBehaviour behv@(Behaviour _ _ (Interface _ decls) _ pre cases post stateUpdates _) =
  behv { _preconditions = pre', _postconditions = post' }
    where
      pre' = pre
             <> mkCallDataBounds decls
             <> mkCalldataLocationBounds clocs
             <> mkStorageBounds stateUpdates Pre
             <> mkStorageBoundsLoc slocs
             <> mkEthEnvBounds (ethEnvFromBehaviour behv)
      post' = post
             <> mkStorageBounds stateUpdates Post

      clocs' = concatMap locsFromExp (pre <> post <> cases)
            <> concatMap locsFromUpdate stateUpdates
      (_, clocs) = partitionLocs clocs'
      slocs' = (nub $ concatMap locsFromExp (pre <> post <> cases) <> concatMap locsFromUpdateRHS stateUpdates)
      (slocs, _) = partitionLocs slocs'

-- | Adds type bounds for calldata, environment vars, and storage vars
addBoundsInvariant :: Constructor -> Invariant -> Invariant
addBoundsInvariant (Constructor _ (Interface _ decls) _ _ _ _ initialStorage) inv@(Invariant _ preconds storagebounds (PredTimed predicate _)) =
  inv { _ipreconditions = preconds', _istoragebounds = storagebounds' }
    where
      preconds' = preconds
                  <> mkCallDataBounds decls
                  <> mkCalldataLocationBounds clocs
                  <> mkEthEnvBounds (ethEnvFromExp predicate)
                  <> mkStorageBoundsLoc externalSLocs
      storagebounds' = storagebounds
                       <> mkStorageBoundsLoc localSLocs

      clocs' = concatMap locsFromExp (preconds <> storagebounds)
                      <> locsFromExp predicate
      (_, clocs) = partitionLocs clocs'
      slocs' = locsFromExp predicate
      (slocs, _) = partitionLocs slocs'
      (localSLocs, externalSLocs) = partition isLocalLoc slocs

mkEthEnvBounds :: [EthEnv] -> [Exp ABoolean]
mkEthEnvBounds vars = catMaybes $ mkBound <$> nub vars
  where
    mkBound :: EthEnv -> Maybe (Exp ABoolean)
    mkBound e = case lookup e globalEnv of
      Just AInteger -> Just $ bound (toAbiType e) (IntEnv nowhere e)
      _ -> Nothing

    toAbiType :: EthEnv -> AbiType
    toAbiType env = case env of
      Caller -> AbiAddressType
      Callvalue -> AbiUIntType 256
      Calldepth -> AbiUIntType 10
      Origin -> AbiAddressType
      Blockhash -> AbiBytesType 32
      Blocknumber -> AbiUIntType 256
      Difficulty -> AbiUIntType 256
      Chainid -> AbiUIntType 256
      Gaslimit -> AbiUIntType 256
      Coinbase -> AbiAddressType
      Timestamp -> AbiUIntType 256
      This -> AbiAddressType
      Nonce -> AbiUIntType 256

-- | Extracts bounds from the AbiTypes of Integer variables in storage
mkStorageBounds :: [StorageUpdate] -> When -> [Exp ABoolean]
mkStorageBounds refs t = concatMap mkBound refs
  where
    mkBound :: StorageUpdate -> [Exp ABoolean]
    mkBound (Update SInteger _ item _) = [mkSItemBounds t item]
    mkBound (Update typ (Shaped _) item@(Item _ (PrimitiveType at) ref) _) = --case flattenAbiType at of
      maybe [] (\Refl -> mkSItemBounds t <$> expandItem item) $ testEquality (fst $ flattenSType typ) SInteger
      --(ba@(FromAbi SInteger), Just shape) -> case ref of
      --  SArray _ r _ i -> (\i' -> mkSItemBounds t $ Item SInteger (PrimitiveType ba) $
      --    SArray nowhere r (PrimitiveType ba) (i ++ (zip ((TExp SInteger Atomic . LitInt nowhere . fromIntegral) <$> i') $ toList shape)) ) <$> exprListIdcs shape
      --  r -> (\i' -> mkSItemBounds t $ Item SInteger (PrimitiveType ba) $
      --    SArray nowhere r (PrimitiveType ba) (zip ((TExp SInteger Atomic . LitInt nowhere . fromIntegral) <$> i') $ toList shape) ) <$> exprListIdcs shape

      --(_, Nothing) -> mkSItemBounds Pre <$> [Item SInteger (PrimitiveType at) ref]
      --(_, _) -> []
    mkBound _ = []

mkSItemBounds :: When -> TItem AInteger Storage -> Exp ABoolean
mkSItemBounds whn item@(Item _ (PrimitiveType vt) _) = bound vt (VarRef nowhere whn SStorage item)
mkSItemBounds _ (Item _ (ContractType _) _) = LitBool nowhere True

mkStorageBoundsLoc :: [StorageLocation] -> [Exp ABoolean]
mkStorageBoundsLoc refs = concatMap mkBound refs
  where
    mkBound :: StorageLocation -> [Exp ABoolean]
    mkBound (SLoc SInteger Atomic item) = [mkSItemBounds Pre item]
    mkBound (SLoc typ (Shaped _) item@(Item _ (PrimitiveType at) ref)) =
      maybe [] (\Refl -> mkSItemBounds Pre <$> expandItem item) $ testEquality (fst $ flattenSType typ) SInteger

      --(ba@(FromAbi SInteger), Just shape) -> case ref of
      --  SArray p r _ i -> (\i' -> mkSItemBounds Pre $ Item SInteger (PrimitiveType ba) $
      --    SArray p r (PrimitiveType ba) (i ++ (zip ((TExp SInteger Nothing . LitInt nowhere . fromIntegral) <$> i') $ toList shape)) ) <$> exprListIdcs shape
      --  r -> (\i' -> mkSItemBounds Pre $ Item SInteger (PrimitiveType ba) $
      --    SArray nowhere r (PrimitiveType ba) (zip ((TExp SInteger Nothing . LitInt nowhere . fromIntegral) <$> i') $ toList shape) ) <$> exprListIdcs shape

      --(_, Nothing) -> mkSItemBounds Pre <$> [Item SInteger (PrimitiveType at) ref]
      --(_, _) -> []
    mkBound _ = []

mkCItemBounds :: TItem AInteger Calldata -> Exp ABoolean
mkCItemBounds item@(Item _ (PrimitiveType vt) _) = bound vt (VarRef nowhere Pre SCalldata item)
mkCItemBounds (Item _ (ContractType _) _) = LitBool nowhere True

mkCalldataLocationBounds :: [CalldataLocation] -> [Exp ABoolean]
mkCalldataLocationBounds refs = concatMap mkBound refs
  where
    mkBound :: CalldataLocation -> [Exp ABoolean]
    mkBound (CLoc SInteger Atomic item) = [mkCItemBounds item]
    mkBound (CLoc typ (Shaped _) item@(Item _ (PrimitiveType at) ref)) = -- case flattenAbiType at of
      maybe [] (\Refl -> mkCItemBounds <$> expandItem item) $ testEquality (fst $ flattenSType typ) SInteger
      --(ba@(FromAbi SInteger), Just shape) -> case ref of
      --  SArray p r _ i -> (\i' -> mkCItemBounds $ Item SInteger (PrimitiveType ba) $
      --    SArray p r (PrimitiveType ba) (i ++ (zip ((TExp SInteger Nothing . LitInt nowhere . fromIntegral) <$> i') $ toList shape)) ) <$> exprListIdcs shape
      --  r -> (\i' -> mkCItemBounds $ Item SInteger (PrimitiveType ba) $
      --    SArray nowhere r (PrimitiveType ba) (zip ((TExp SInteger Nothing . LitInt nowhere . fromIntegral) <$> i') $ toList shape) ) <$> exprListIdcs shape

      --(_, Nothing) -> mkCItemBounds <$> [Item SInteger (PrimitiveType at) ref]
      --(_, _) -> []
    mkBound _ = []

mkCallDataBounds :: [Decl] -> [Exp ABoolean]
mkCallDataBounds = concatMap $ \(Decl typ name) -> case typ of
  -- Array element bounds are applied lazily when needed in mkCalldataLocationBounds
  (AbiArrayType _ _) -> []
  _ -> case fromAbiType typ of
        AInteger -> [bound typ (_Var typ name)]
        _ -> []
