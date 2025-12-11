{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

{-|
Module      : Syntax
Description : Functions for manipulating and collapsing all our different ASTs.
-}
module Act.Syntax where

import Prelude hiding (LT, GT)

import Data.List hiding (singleton)
import Data.Maybe (mapMaybe)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Map (Map,empty,insertWith,unionsWith,unionWith,singleton)

import Act.Syntax.Typed as Typed
import qualified Act.Syntax.TypedExplicit as TypedExplicit
import           Act.Syntax.Untyped hiding (Contract, Constructor, Update, Ref(..), StorageUpdate)
import qualified Act.Syntax.Untyped as Untyped

-----------------------------------------
-- * Extract from fully refined ASTs * --
-----------------------------------------


-- | Invariant predicates can always be expressed as a single expression.
invExp :: TypedExplicit.InvariantPred -> TypedExplicit.Exp ABoolean
invExp (PredTimed pre post) = pre <> post

locsFromBehaviour :: TypedExplicit.Behaviour -> [TypedExplicit.TypedRef]
locsFromBehaviour (Behaviour _ _ _ _ preconds cases postconds) = nub $
  concatMap locsFromExp preconds
  <> concatMap locsFromExp postconds
  <> concatMap locsFromCase cases

locsFromCase :: (TypedExplicit.Exp ABoolean, ([TypedExplicit.StorageUpdate], Maybe (TypedExplicit.TypedExp))) -> [TypedExplicit.TypedRef]
locsFromCase (cond, (rewrites, mret)) = nub $
  locsFromExp cond <> concatMap locsFromUpdate rewrites <> maybe [] locsFromTypedExp mret

locsFromConstructor :: TypedExplicit.Constructor -> [TypedExplicit.TypedRef]
locsFromConstructor (TypedExplicit.Constructor _ _ _ pre cases post inv) = nub $
  concatMap locsFromExp pre
  <> concatMap locsFromExp post
  <> concatMap locsFromConstrInvariant inv
  <> concatMap locsFromConstrCase cases

locsFromConstrCase :: (TypedExplicit.Exp ABoolean, [TypedExplicit.StorageUpdate]) -> [TypedExplicit.TypedRef]
locsFromConstrCase (cond, creates) = nub $
  locsFromExp cond <> concatMap locsFromUpdate creates

locsFromInvariant :: TypedExplicit.Invariant -> [TypedExplicit.TypedRef]
locsFromInvariant (Invariant _ pre bounds (PredTimed predpre predpost)) =
  concatMap locsFromExp pre <>  concatMap locsFromExp bounds
  <> locsFromExp predpre <> locsFromExp predpost

locsFromConstrInvariant :: TypedExplicit.Invariant -> [TypedExplicit.TypedRef]
locsFromConstrInvariant (Invariant _ pre _ (PredTimed _ predpost)) =
  concatMap locsFromExp pre <> locsFromExp predpost

------------------------------------
-- * Extract from any typed AST * --
------------------------------------

nameOfContract :: Contract t -> Id
nameOfContract (Contract (Constructor cname _ _ _ _ _ _) _) = cname

behvsFromAct :: Typed.Act t -> [Behaviour t]
behvsFromAct (Act _ contracts) = behvsFromContracts contracts

behvsFromContracts :: [Contract t] -> [Behaviour t]
behvsFromContracts contracts = concatMap (\(Contract _ b) -> b) contracts

constrFromContracts :: [Contract t] -> [Constructor t]
constrFromContracts contracts = fmap (\(Contract c _) -> c) contracts

isStorageTRef :: TypedRef t -> Bool
isStorageTRef (TRef _ _ ref) = isLocalRef ref

isLocalRef :: Ref k t -> Bool
isLocalRef (SVar _ _ _ _) = True
isLocalRef (CVar _ _ _) = False
isLocalRef (RArrIdx _ ref _ _) = isLocalRef ref
isLocalRef (RMapIdx _ (TRef _ _ ref) _) = isLocalRef ref
isLocalRef (RField _ _ _ _) = False

isCalldata :: Ref k t -> Bool
isCalldata (SVar _ _ _ _) = False
isCalldata (CVar _ _ _) = True
isCalldata (RArrIdx _ ref _ _) = isCalldata ref
isCalldata (RMapIdx _ (TRef _ _ ref) _) = isCalldata ref
isCalldata (RField _ r _ _) = isCalldata r

-- Zoe: not sure what's the correct definition
-- Lefteris: may not be necessary but works for now
partitionLocs :: [TypedRef t] -> ([TypedRef t], [TypedRef t])
partitionLocs locs = foldMap sepTRef locs
  where
    sepTRef :: TypedRef t -> ([TypedRef t], [TypedRef t])
    sepTRef tref@(TRef _ _ r) | isCalldata r = ([],[tref])
    sepTRef tref@(TRef _ _ _) = ([tref],[])

locsFromUpdate :: StorageUpdate t -> [TypedRef t]
locsFromUpdate update = nub $ case update of
  (Update t ref e) -> locsFromTRef (TRef t SLHS ref) <> locsFromExp e

locsFromUpdateRHS :: StorageUpdate t -> [TypedRef t]
locsFromUpdateRHS update = nub $ case update of
  (Update _ _ e) -> locsFromExp e

locFromUpdate :: StorageUpdate t -> Ref LHS t
locFromUpdate (Update _ item _) = item

locsFromTRef :: TypedRef t -> [TypedRef t]
locsFromTRef ref@(TRef (toSType -> SType) _ _) = ref : concatMap locsFromTypedExp (ixsFromTRef ref)

locsFromTypedExp :: TypedExp t -> [TypedRef t]
locsFromTypedExp (TExp _ e) = locsFromExp e

locsFromExp :: Exp a t -> [TypedRef t]
locsFromExp = nub . go
  where
    go :: Exp a t -> [TypedRef t]
    go e = case e of
      And _ a b   -> go a <> go b
      Or _ a b    -> go a <> go b
      Impl _ a b  -> go a <> go b
      Eq _ _ a b    -> go a <> go b
      LT _ a b    -> go a <> go b
      LEQ _ a b   -> go a <> go b
      GT _ a b    -> go a <> go b
      GEQ _ a b   -> go a <> go b
      NEq _ _ a b   -> go a <> go b
      Neg _ a     -> go a
      Add _ a b   -> go a <> go b
      Sub _ a b   -> go a <> go b
      Mul _ a b   -> go a <> go b
      Div _ a b   -> go a <> go b
      Mod _ a b   -> go a <> go b
      Exp _ a b   -> go a <> go b
      Array _ l -> concatMap go l
      Cat _ a b   -> go a <> go b
      Slice _ a b c -> go a <> go b <> go c
      ByStr {} -> []
      ByLit {} -> []
      LitInt {}  -> []
      IntMin {}  -> []
      IntMax {}  -> []
      UIntMin {} -> []
      UIntMax {} -> []
      InRange _ _ a -> go a
      LitBool {} -> []
      IntEnv {} -> []
      ByEnv {} -> []
      Create _ _ es _ -> concatMap locsFromTypedExp es
      ITE _ x y z -> go x <> go y <> go z
      VarRef _ vt a -> locsFromTRef (TRef vt SRHS a)
      Address _ _ e' -> locsFromExp e'
      Typed.Mapping _ _ _ kvs -> concatMap (\(k', v') -> go k' <> go v') kvs
      Typed.MappingUpd _ r t1@VType t2@VType kvs -> 
        locsFromTRef (TRef (TMapping (ValueType t1) (ValueType t2)) SLHS r) <> concatMap (\(k', v') -> go k' <> go v') kvs

createsFromExp :: Exp a t -> [Id]
createsFromExp = nub . go
  where
    go :: Exp a t -> [Id]
    go e = case e of
      And _ a b   -> go a <> go b
      Or _ a b    -> go a <> go b
      Impl _ a b  -> go a <> go b
      Eq _ _ a b    -> go a <> go b
      LT _ a b    -> go a <> go b
      LEQ _ a b   -> go a <> go b
      GT _ a b    -> go a <> go b
      GEQ _ a b   -> go a <> go b
      NEq _ _ a b   -> go a <> go b
      Neg _ a     -> go a
      Add _ a b   -> go a <> go b
      Sub _ a b   -> go a <> go b
      Mul _ a b   -> go a <> go b
      Div _ a b   -> go a <> go b
      Mod _ a b   -> go a <> go b
      Exp _ a b   -> go a <> go b
      Cat _ a b   -> go a <> go b
      Slice _ a b c -> go a <> go b <> go c
      ByStr {} -> []
      ByLit {} -> []
      LitInt {}  -> []
      IntMin {}  -> []
      IntMax {}  -> []
      UIntMin {} -> []
      UIntMax {} -> []
      InRange _ _ a -> go a
      LitBool {} -> []
      IntEnv {} -> []
      ByEnv {} -> []
      Array _ l  -> concatMap go l
      Create _ f es _ -> [f] <> concatMap createsFromTypedExp es
      ITE _ x y z -> go x <> go y <> go z
      VarRef _ vt a -> createsFromTRef (TRef vt SRHS a)
      Address _ _ e' -> createsFromExp e'
      Typed.Mapping _ _ _ kvs -> concatMap (\(k', v') -> go k' <> go v') kvs
      Typed.MappingUpd _ r t1@VType t2@VType kvs ->
        createsFromTRef (TRef (TMapping (ValueType t1) (ValueType t2)) SLHS r) <> concatMap (\(k', v') -> go k' <> go v') kvs

createsFromTRef :: TypedRef t -> [Id]
createsFromTRef ref = concatMap createsFromTypedExp (ixsFromTRef ref)

createsFromTypedExp :: TypedExp t -> [Id]
createsFromTypedExp (TExp _ e) = createsFromExp e

createsFromContract :: Contract t -> [Id]
createsFromContract (Contract constr behvs) =
  createsFromConstructor constr <> concatMap createsFromBehaviour behvs

createsFromConstrCase :: (Exp ABoolean t, [StorageUpdate t]) -> [Id]
createsFromConstrCase (cond, rewrites) = nub $
  createsFromExp cond <> concatMap createsFromUpdate rewrites

createsFromConstructor :: Constructor t -> [Id]
createsFromConstructor (Constructor _ _ _ pre cases post inv) = nub $
  concatMap createsFromExp pre
  <> concatMap createsFromExp post
  <> concatMap createsFromInvariant inv
  <> concatMap createsFromConstrCase cases

createsFromInvariant :: Invariant t -> [Id]
createsFromInvariant (Invariant _ pre bounds ipred) =
  concatMap createsFromExp pre <>  concatMap createsFromExp bounds <> createsFromInvariantPred ipred

createsFromInvariantPred :: InvariantPred t -> [Id]
createsFromInvariantPred (PredUntimed p) = createsFromExp p
createsFromInvariantPred (PredTimed pre post) = createsFromExp pre <> createsFromExp post

createsFromUpdate :: StorageUpdate t ->[Id]
createsFromUpdate update = nub $ case update of
  TypedExplicit.Update t ref e -> createsFromTRef (TRef t SLHS ref) <> createsFromExp e

createsFromCase :: (Exp ABoolean t, ([StorageUpdate t], Maybe (TypedExp t))) -> [Id]
createsFromCase (cond, (rewrites, mret)) = nub $
  createsFromExp cond <> concatMap createsFromUpdate rewrites <> maybe [] createsFromTypedExp mret

createsFromBehaviour :: Behaviour t -> [Id]
createsFromBehaviour (Behaviour _ _ _ _ preconds cases postconds) = nub $
  concatMap createsFromExp preconds
  <> concatMap createsFromExp postconds
  <> concatMap createsFromCase cases


pointersFromContract :: Contract t -> [Id]
pointersFromContract (Contract constr behvs) =
  nub $ pointersFromConstructor constr <> concatMap pointersFromBehaviour behvs

pointersFromConstructor :: Constructor t -> [Id]
pointersFromConstructor (Constructor _ (Interface _ decls) _ _ _ _ _) =
  mapMaybe (fmap snd . pointerFromDecl) decls

pointersFromBehaviour :: Behaviour t -> [Id]
pointersFromBehaviour (Behaviour _ _ (Interface _ decls) _ _ _ _) =
  mapMaybe (fmap snd . pointerFromDecl) decls

pointerFromDecl :: Arg -> Maybe (Id, Id)
pointerFromDecl (Arg (ContractArg _ c) name) = Just (name,c)
pointerFromDecl _ = Nothing

ethEnvFromCase :: (Exp ABoolean t, ([StorageUpdate t], Maybe (TypedExp t))) -> [EthEnv]
ethEnvFromCase (cond, (rewrites, mret)) = nub $
  ethEnvFromExp cond <> concatMap ethEnvFromUpdate rewrites <> maybe [] ethEnvFromTypedExp mret

ethEnvFromBehaviour :: Behaviour t -> [EthEnv]
ethEnvFromBehaviour (Behaviour _ _ _ _ preconds cases postconds) = nub $
  concatMap ethEnvFromExp preconds
  <> concatMap ethEnvFromCase cases
  <> concatMap ethEnvFromExp postconds

ethEnvFromConstrCase :: (Exp ABoolean t, [StorageUpdate t]) -> [EthEnv]
ethEnvFromConstrCase (cond, rewrites) = nub $
  ethEnvFromExp cond <> concatMap ethEnvFromUpdate rewrites

ethEnvFromConstructor :: TypedExplicit.Constructor -> [EthEnv]
ethEnvFromConstructor (TypedExplicit.Constructor _ _ _ pre cases post inv) = nub $
  concatMap ethEnvFromExp pre
  <> concatMap ethEnvFromExp post
  <> concatMap ethEnvFromInvariant inv
  <> concatMap ethEnvFromConstrCase cases

ethEnvFromInvariant :: TypedExplicit.Invariant -> [EthEnv]
ethEnvFromInvariant (Invariant _ pre bounds invpred) =
  concatMap ethEnvFromExp pre <>  concatMap ethEnvFromExp bounds <> ethEnvFromInvariantPred invpred

ethEnvFromInvariantPred :: InvariantPred t -> [EthEnv]
ethEnvFromInvariantPred (PredUntimed p) = ethEnvFromExp p
ethEnvFromInvariantPred (PredTimed pre post) = ethEnvFromExp pre <> ethEnvFromExp post

ethEnvFromUpdate :: StorageUpdate t -> [EthEnv]
ethEnvFromUpdate rewrite = case rewrite of
  TypedExplicit.Update t ref e -> nub $ ethEnvFromItem (TRef t SLHS ref) <> ethEnvFromExp e

ethEnvFromItem :: TypedRef t -> [EthEnv]
ethEnvFromItem = nub . concatMap ethEnvFromTypedExp . ixsFromTRef

ethEnvFromTypedExp :: TypedExp t -> [EthEnv]
ethEnvFromTypedExp (TExp _ e) = ethEnvFromExp e

ethEnvFromExp :: Exp a t -> [EthEnv]
ethEnvFromExp = nub . go
  where
    go :: Exp a t -> [EthEnv]
    go e = case e of
      And   _ a b   -> go a <> go b
      Or    _ a b   -> go a <> go b
      Impl  _ a b   -> go a <> go b
      Eq    _ _ a b   -> go a <> go b
      LT    _ a b   -> go a <> go b
      LEQ   _ a b   -> go a <> go b
      GT    _ a b   -> go a <> go b
      GEQ   _ a b   -> go a <> go b
      NEq   _ _ a b   -> go a <> go b
      Neg   _ a     -> go a
      Add   _ a b   -> go a <> go b
      Sub   _ a b   -> go a <> go b
      Mul   _ a b   -> go a <> go b
      Div   _ a b   -> go a <> go b
      Mod   _ a b   -> go a <> go b
      Exp   _ a b   -> go a <> go b
      Array _ l -> concatMap go l
      Cat   _ a b   -> go a <> go b
      Slice _ a b c -> go a <> go b <> go c
      ITE   _ a b c -> go a <> go b <> go c
      ByStr {} -> []
      ByLit {} -> []
      LitInt {}  -> []
      LitBool {} -> []
      IntMin {} -> []
      IntMax {} -> []
      UIntMin {} -> []
      UIntMax {} -> []
      InRange _ _ a -> go a
      IntEnv _ a -> [a]
      ByEnv _ a -> [a]
      Create _ _ ixs _ -> concatMap ethEnvFromTypedExp ixs
      VarRef _ _ a -> concatMap ethEnvFromTypedExp (ixsFromRef a)
      Address _ _ e' -> ethEnvFromExp e'
      Typed.Mapping _ _ _ kvs -> concatMap (\(k', v') -> go k' <> go v') kvs
      Typed.MappingUpd _ r _ _ kvs -> concatMap ethEnvFromTypedExp (ixsFromRef r) <> concatMap (\(k', v') -> go k' <> go v') kvs

idFromTRef :: TypedRef t -> Id
idFromTRef (TRef _ _ ref) = idFromRef ref

idFromRef :: Ref k t -> Id
idFromRef (SVar _ _ _ x) = x
idFromRef (CVar _ _ x) = x
idFromRef (RArrIdx _ e _ _) = idFromRef e
idFromRef (RMapIdx _ (TRef _ _ e) _) = idFromRef e
idFromRef (RField _ e _ _) = idFromRef e

idFromUpdate :: StorageUpdate t -> Id
idFromUpdate (TypedExplicit.Update _ ref _) = idFromRef ref

-- Used to compare all identifiers in a location access
idsFromTRef :: TypedRef t -> [String]
idsFromTRef (TRef _ _ ref) = idsFromRef ref

idsFromRef :: Ref k t -> [String]
idsFromRef (SVar _ _ _ x) = [x]
idsFromRef (CVar _ _ x) = [x]
idsFromRef (RArrIdx _ e _ _) = idsFromRef e
idsFromRef (RMapIdx _ (TRef _ _ e) _) = idsFromRef e
idsFromRef (RField _ e _ f) = f : idsFromRef e

ixsFromTRef :: TypedRef t -> [TypedExp t]
ixsFromTRef (TRef _ _ item) = ixsFromRef item

ixsFromRef :: Ref k t -> [TypedExp t]
ixsFromRef (SVar _ _ _ _) = []
ixsFromRef (CVar _ _ _) = []
ixsFromRef (RArrIdx _ ref ix _) = (TExp defaultUInteger ix) : ixsFromRef ref
ixsFromRef (RMapIdx _ (TRef _ _ ref) ix) = ix : ixsFromRef ref
ixsFromRef (RField _ ref _ _) = ixsFromRef ref

ixsFromUpdate :: StorageUpdate t -> [TypedExp t]
ixsFromUpdate (TypedExplicit.Update _ ref _) = ixsFromRef ref

--itemType :: TypedRef t -> TValueType a
--itemType (TRef t _ _) = t -- fromAbiType $ toAbiType t -- TODO: cleanup, residue from STYPEs

isIndexed :: TypedRef t -> Bool
isIndexed ref = isArrayTRef ref || isMappingTRef ref

isArrayTRef :: TypedRef t -> Bool
isArrayTRef (TRef _ _ ref) = isArrayRef ref

isArrayRef :: Ref k t -> Bool
isArrayRef (SVar _ _ _ _) = False
isArrayRef (CVar _ _ _) = False
isArrayRef (RArrIdx _ _ _ _) = True
isArrayRef (RMapIdx _ _ _) = False  -- may change in the future
isArrayRef (RField _ ref _ _) = isArrayRef ref

isMappingTRef :: TypedRef t -> Bool
isMappingTRef (TRef _ _ ref) = isMappingRef ref

isMappingRef :: Ref k t -> Bool
isMappingRef (SVar _ _ _ _) = False
isMappingRef (CVar _ _ _) = False
isMappingRef (RArrIdx _ _ _ _) = False  -- may change in the future
isMappingRef (RMapIdx _ _ _) = True
isMappingRef (RField _ ref _ _) = isMappingRef ref

posnFromExp :: Exp a t -> Pn
posnFromExp e = case e of
  And p _ _ -> p
  Or p _ _ -> p
  Impl p _ _ -> p
  Neg p _ -> p
  LT p _ _ -> p
  LEQ p _ _ -> p
  GEQ p _ _ -> p
  GT p _ _ -> p
  LitBool p _ -> p
  -- integers
  Add p _ _ -> p
  Sub p _ _ -> p
  Mul p _ _ -> p
  Div p _ _ -> p
  Mod p _ _ -> p
  Exp p _ _ -> p
  LitInt p _ -> p
  IntEnv p _ -> p
  -- bounds
  IntMin p _ -> p
  IntMax p _ -> p
  UIntMin p _ -> p
  UIntMax p _ -> p
  InRange p _ _ -> p

  Array p _ -> p

  -- bytestrings
  Cat p _ _ -> p
  Slice p _ _ _ -> p
  ByStr p _ -> p
  ByLit p _ -> p
  ByEnv p _ -> p
  -- contracts
  Create p _ _ _ -> p

  -- polymorphic
  Eq  p _ _ _ -> p
  NEq p _ _ _ -> p
  ITE p _ _ _ -> p
  VarRef p _ _ -> p
  Address _ _ e' -> posnFromExp e'
  Typed.Mapping p _ _ _ -> p
  Typed.MappingUpd p _ _ _ _ -> p

posnFromTRef :: TypedRef t -> Pn
posnFromTRef (TRef _ _ ref) = posnFromRef ref

posnFromRef :: Ref a k -> Pn
posnFromRef (CVar p _ _) = p
posnFromRef (SVar p _ _ _) = p
posnFromRef (RArrIdx p _ _ _) = p
posnFromRef (RMapIdx p _ _) = p
posnFromRef (RField p _ _ _) = p

-- | Given the shape of a nested array (outer to inner lengths)
-- returns an array of all indices
arrayIdcs :: NonEmpty.NonEmpty Int -> [[Int]]
arrayIdcs typ = map idx [0..(len - 1)]
  where
    -- The result of scanr is always non-empty
    (len NonEmpty.:| typeAcc) = NonEmpty.scanr (*) 1 typ
    idx e = zipWith (\ x1 x2 -> (e `div` x2) `mod` x1) (NonEmpty.toList typ) typeAcc

-- | Expand an array item to a list of items of its elements,
-- or an atomic item to a singleton list of itself.
-- The returned elements follow increasing numerical order
-- when interpreting the indices as digits of decreasing
-- significance from outermost to innermost.
expandTRef :: TValueType a -> Ref k t -> [Ref k t]
expandTRef typ ref = go typ [ref]
  where
  go :: TValueType a -> [Ref k t] -> [Ref k t]
  go (TArray n t) rs = go t (concatMap (\r -> ((\i -> RArrIdx nowhere r (LitInt nowhere $ fromIntegral i) n) <$> [0..n])) rs)
  go _ rs = rs

-- | Expand an array expression to a list of expressions of its elements,
-- The order of the returned elements is the same as 'expandItem's
expandArrayExpr :: TValueType (AArray a) -> Exp (AArray a) t -> [Exp (Base (AArray a)) t]
expandArrayExpr (TArray _ (TInteger _ _)) (Array _ l) = l
expandArrayExpr (TArray _ TUnboundedInt) (Array _ l) = l
expandArrayExpr (TArray _ TAddress) (Array _ l) = l
expandArrayExpr (TArray _ TBoolean) (Array _ l) = l
expandArrayExpr (TArray _ TByteStr) (Array _ l) = l
expandArrayExpr (TArray _ (TStruct _)) (Array _ l) = l
expandArrayExpr (TArray _ (TContract _)) (Array _ l) = l
expandArrayExpr (TArray _ (TMapping _ _)) (Array _ _) = error "expandArrayExpr: arrays of mappings not supported"
expandArrayExpr (TArray _ s@(TArray _ _)) (Array _ l) = concatMap (expandArrayExpr s) l
expandArrayExpr _ (VarRef pn vt ref) = 
  case expandTRef vt ref of
    expandedRefs -> (VarRef pn btyp) <$> expandedRefs
  where btyp = fst $ flattenValueType vt
expandArrayExpr typ (ITE pn tbool e1 e2) =
  (uncurry $ ITE pn tbool) <$> zip (expandArrayExpr typ e1) (expandArrayExpr typ e2)

--------------------------------------
-- * Extraction from untyped ASTs * --
--------------------------------------

nameFromStorage :: Untyped.StorageUpdate -> Id
nameFromStorage (Untyped.Update e _) = nameFromEntry e

nameFromEntry :: Untyped.Ref -> Id
nameFromEntry (Untyped.RVar _ _ x) = x
nameFromEntry (Untyped.RIndex _ e _) = nameFromEntry e
nameFromEntry (Untyped.RField _ e _) = nameFromEntry e

getPosRef :: Untyped.Ref -> Pn
getPosRef (Untyped.RVar pn _ _) = pn
getPosRef (Untyped.RIndex pn _ _) = pn
getPosRef (Untyped.RField pn _ _) = pn

getPosn :: Untyped.Expr -> Pn
getPosn expr = case expr of
    Untyped.EAnd pn  _ _ -> pn
    Untyped.EOr pn _ _ -> pn
    Untyped.ENot pn _ -> pn
    Untyped.EImpl pn _ _ -> pn
    Untyped.EEq pn _ _ -> pn
    Untyped.ENeq pn _ _ -> pn
    Untyped.ELEQ pn _ _ -> pn
    Untyped.ELT pn _ _ -> pn
    Untyped.EGEQ pn _ _ -> pn
    Untyped.EGT pn _ _ -> pn
    Untyped.EAdd pn _ _ -> pn
    Untyped.ESub pn _ _ -> pn
    Untyped.EITE pn _ _ _ -> pn
    Untyped.EMul pn _ _ -> pn
    Untyped.EDiv pn _ _ -> pn
    Untyped.EMod pn _ _ -> pn
    Untyped.EExp pn _ _ -> pn
    Untyped.ECreate pn _ _ _ -> pn
    Untyped.AddrOf pn _ -> pn
    Untyped.ERef e -> getPosRef e
    Untyped.EArray pn _ -> pn
    Untyped.ListConst e -> getPosn e
    Untyped.ECat pn _ _ -> pn
    Untyped.ESlice pn _ _ _ -> pn
    Untyped.ENewaddr pn _ _ -> pn
    Untyped.ENewaddr2 pn _ _ _ -> pn
    Untyped.BYHash pn _ -> pn
    Untyped.BYAbiE pn _ -> pn
    Untyped.StringLit pn _ -> pn
    Untyped.WildExp pn -> pn
    Untyped.EnvExp pn _ -> pn
    Untyped.IntLit pn _ -> pn
    Untyped.BoolLit pn _ -> pn
    Untyped.EInRange pn _ _ -> pn
    Untyped.Mapping pn _ -> pn
    Untyped.MappingUpd pn _ _ -> pn

--posFromDef :: Mapping -> Pn
--posFromDef (Mapping e _) = getPosn e

-- | Returns all the identifiers used in an expression,
-- as well all of the positions they're used in.
idFromRewrites :: Untyped.Expr -> Map Id [Pn]
idFromRewrites e = case e of
  Untyped.EAnd _ a b        -> idFromRewrites' [a,b]
  Untyped.EOr _ a b         -> idFromRewrites' [a,b]
  Untyped.ENot _ a          -> idFromRewrites a
  Untyped.EImpl _ a b       -> idFromRewrites' [a,b]
  Untyped.EEq _ a b         -> idFromRewrites' [a,b]
  Untyped.ENeq _ a b        -> idFromRewrites' [a,b]
  Untyped.ELEQ _ a b        -> idFromRewrites' [a,b]
  Untyped.ELT _ a b         -> idFromRewrites' [a,b]
  Untyped.EGEQ _ a b        -> idFromRewrites' [a,b]
  Untyped.EGT _ a b         -> idFromRewrites' [a,b]
  Untyped.EAdd _ a b        -> idFromRewrites' [a,b]
  Untyped.ESub _ a b        -> idFromRewrites' [a,b]
  Untyped.EITE _ a b c      -> idFromRewrites' [a,b,c]
  Untyped.EMul _ a b        -> idFromRewrites' [a,b]
  Untyped.EDiv _ a b        -> idFromRewrites' [a,b]
  Untyped.EMod _ a b        -> idFromRewrites' [a,b]
  Untyped.EExp _ a b        -> idFromRewrites' [a,b]
  Untyped.ERef en           -> idFromRef' en
  Untyped.EArray _ l        -> idFromRewrites' l
  Untyped.ListConst a       -> idFromRewrites a
  Untyped.ECat _ a b        -> idFromRewrites' [a,b]
  Untyped.ESlice _ a b c    -> idFromRewrites' [a,b,c]
  Untyped.ENewaddr _ a b    -> idFromRewrites' [a,b]
  Untyped.ENewaddr2 _ a b c -> idFromRewrites' [a,b,c]
  Untyped.BYHash _ a        -> idFromRewrites a
  Untyped.BYAbiE _ a        -> idFromRewrites a
  Untyped.StringLit {}      -> empty
  Untyped.WildExp {}        -> empty
  Untyped.EnvExp {}         -> empty
  Untyped.IntLit {}         -> empty
  Untyped.BoolLit {}        -> empty
  Untyped.EInRange _ _ a    -> idFromRewrites a
  Untyped.ECreate p x es (Just pm) -> insertWith (<>) x [p] $ idFromRewrites' (pm : es)
  Untyped.ECreate p x es Nothing   -> insertWith (<>) x [p] $ idFromRewrites' es
  Untyped.AddrOf _ a        -> idFromRewrites a
  Untyped.Mapping _ a       -> idFromRewrites' $ concatMap (\(x,y) -> [x,y]) a
  Untyped.MappingUpd _ r a  -> unionsWith (<>) [idFromRef' r, idFromRewrites' $ concatMap (\(x,y) -> [x,y]) a]
  where
    idFromRewrites' = unionsWith (<>) . fmap idFromRewrites

    idFromRef' :: Untyped.Ref -> Map Id [Pn]
    idFromRef' (Untyped.RVar p _ x) = singleton x [p]
    idFromRef' (Untyped.RIndex _ en x) = unionWith (<>) (idFromRef' en) (idFromRewrites x)
    idFromRef' (Untyped.RField _ en _) = idFromRef' en

-- | True iff the case is a wildcard.
isWild :: Untyped.Case t -> Bool
isWild (Untyped.Case _ (WildExp _) _) = True
isWild _                      = False

bound :: TValueType AInteger -> Exp AInteger t -> Exp ABoolean t
bound typ e = And nowhere (LEQ nowhere (lowerBound typ) e) $ LEQ nowhere e (upperBound typ)

lowerBound :: forall t. TValueType AInteger -> Exp AInteger t
lowerBound (TInteger a Signed) = IntMin nowhere a
-- TODO: other negatives?
lowerBound _ = LitInt nowhere 0

-- TODO, the rest
upperBound :: forall t. TValueType AInteger -> Exp AInteger t
upperBound (TInteger n Unsigned) = UIntMax nowhere n
upperBound (TInteger n Signed) = IntMax nowhere n
upperBound TAddress   = UIntMax nowhere 160
upperBound t = error $ "upperBound: no upper bound defined for type" <> show t

defaultInteger :: TValueType AInteger
defaultInteger = TInteger 256 Signed

defaultUInteger :: TValueType AInteger
defaultUInteger = TInteger 256 Unsigned
