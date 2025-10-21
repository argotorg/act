{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module Act.Bounds (addBounds, mkLocationBounds) where

import Data.Maybe
import Data.List (nub, partition)
import Data.Type.Equality

import Act.Syntax
import Act.Syntax.TypedExplicit
import Act.Type (globalEnv)


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
addBoundsConstructor ctor@(Constructor _ (Interface _ decls) pre post invs stateUpdates) =
  ctor { _cpreconditions = pre'
       , _cpostconditions = post'
       , _invariants = invs' }
    where
      pre' = nub $ pre
             <> mkCallDataBounds decls
             <> mkEthEnvBounds (ethEnvFromConstructor ctor)
              -- The following is sound as values of locations outside local storage
              -- already exist as the constructor starts executing,
              -- and the constructor cannot modify non-local locations.
             <> mkLocationBounds nonlocalLocs
      invs' = addBoundsInvariant ctor <$> invs
      post' = post <> mkStorageBounds stateUpdates Post

      locs = nub $ concatMap locsFromExp (pre <> post)
             <> concatMap locsFromInvariant invs
             <> concatMap locsFromUpdate stateUpdates
      nonlocalLocs = filter (not . isLocalLoc) locs

-- | Adds type bounds for calldata, environment vars, and storage vars as preconditions
addBoundsBehaviour :: Behaviour -> Behaviour
addBoundsBehaviour behv@(Behaviour _ _ (Interface _ decls) pre cases post stateUpdates ret) =
  behv { _preconditions = pre', _postconditions = post' }
    where
      pre' = nub $ pre
             <> mkCallDataBounds decls
             <> mkStorageBounds stateUpdates Pre
             <> mkLocationBounds locs
             <> mkEthEnvBounds (ethEnvFromBehaviour behv)
      post' = post
              <> mkStorageBounds stateUpdates Post

      locs = nub $ concatMap locsFromExp (pre <> post <> cases)
             <> concatMap locsFromUpdate stateUpdates
             <> (maybe [] locsFromTypedExp ret)

-- | Adds type bounds for calldata, environment vars, and storage vars
addBoundsInvariant :: Constructor -> Invariant -> Invariant
addBoundsInvariant (Constructor _ (Interface _ decls) _ _ _ _) inv@(Invariant _ preconds storagebounds (PredTimed predicate _)) =
  inv { _ipreconditions = preconds', _istoragebounds = storagebounds' }
    where
      preconds' = nub $ preconds
                  <> mkCallDataBounds decls
                  <> mkEthEnvBounds (ethEnvFromExp predicate)
                  <> mkLocationBounds nonlocalLocs
      storagebounds' = storagebounds
                       <> mkLocationBounds localLocs

      locs = nub $ concatMap locsFromExp (preconds <> storagebounds)
             <> locsFromExp predicate
      (nonlocalLocs, localLocs) = partition (not . isLocalLoc) locs

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
    mkBound (Update SInteger item _) = [mkSItemBounds t item]
    mkBound (Update typ item@(Item _ (PrimitiveType at) _) _) | isJust $ flattenArrayAbiType at =
      maybe [] (\Refl -> mkSItemBounds t <$> expandItem item) $ testEquality (flattenSType typ) SInteger
    mkBound _ = []

mkSItemBounds :: When -> TItem AInteger Storage -> Exp ABoolean
mkSItemBounds whn item@(Item _ (PrimitiveType vt) _) = bound vt (VarRef nowhere whn SStorage item)
mkSItemBounds _ (Item _ (ContractType _) _) = LitBool nowhere True

mkCItemBounds :: TItem AInteger Calldata -> Exp ABoolean
mkCItemBounds item@(Item _ (PrimitiveType vt) _) = bound vt (VarRef nowhere Pre SCalldata item)
mkCItemBounds (Item _ (ContractType _) _) = LitBool nowhere True

mkLocationBounds :: [Location] -> [Exp ABoolean]
mkLocationBounds refs = concatMap mkBound refs
  where
    mkBound :: Location -> [Exp ABoolean]
    mkBound (Loc SInteger rk item) = [mkItemBounds rk item]
    mkBound (Loc typ rk item@(Item _ (PrimitiveType at) _)) | isJust $ flattenArrayAbiType at =
      maybe [] (\Refl -> mkItemBounds rk <$> expandItem item) $ testEquality (flattenSType typ) SInteger
    mkBound _ = []

    mkItemBounds :: SRefKind k -> TItem AInteger k -> Exp ABoolean
    mkItemBounds SStorage = mkSItemBounds Pre
    mkItemBounds SCalldata = mkCItemBounds

mkCallDataBounds :: [Decl] -> [Exp ABoolean]
mkCallDataBounds = concatMap $ \(Decl argtyp name) -> case argtyp of
  (AbiArg typ) ->
    case typ of
      -- Array element bounds are applied lazily when needed in mkCalldataLocationBounds
      (AbiArrayType _ _) -> []
      _ -> case fromAbiType typ of
            AInteger -> [bound typ (_Var typ name)]
            _ -> []
  (ContractArg _ cid) -> [bound AbiAddressType (Address cid (_Var AbiAddressType name))]
