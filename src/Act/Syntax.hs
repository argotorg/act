{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

{-|
Module      : Syntax
Description : Functions for manipulating and collapsing all our different ASTs.
-}
module Act.Syntax where

import Prelude hiding (LT, GT)

import Data.Type.Equality
import Data.List hiding (singleton)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Map (Map,empty,insertWith,unionsWith,unionWith,singleton)

import Act.Syntax.Typed as Typed
import qualified Act.Syntax.TypedExplicit as TypedExplicit
import           Act.Syntax.Untyped hiding (Contract, Constructor, Post, Update)
import qualified Act.Syntax.Untyped as Untyped

-----------------------------------------
-- * Extract from fully refined ASTs * --
-----------------------------------------


-- | Invariant predicates can always be expressed as a single expression.
invExp :: TypedExplicit.InvariantPred -> TypedExplicit.Exp ABoolean
invExp (PredTimed pre post) = pre <> post

locsFromBehaviour :: TypedExplicit.Behaviour -> [TypedExplicit.Location]
locsFromBehaviour (Behaviour _ _ _ _ preconds cases postconds rewrites returns) = nub $
  concatMap locsFromExp preconds
  <> concatMap locsFromExp cases
  <> concatMap locsFromExp postconds
  <> concatMap locsFromUpdate rewrites
  <> maybe [] locsFromTypedExp returns

locsFromConstructor :: TypedExplicit.Constructor -> [TypedExplicit.Location]
locsFromConstructor (TypedExplicit.Constructor _ _ _ pre post inv initialStorage) = nub $
  concatMap locsFromExp pre
  <> concatMap locsFromExp post
  <> concatMap locsFromConstrInvariant inv
  <> concatMap locsFromUpdate initialStorage

locsFromInvariant :: TypedExplicit.Invariant -> [TypedExplicit.Location]
locsFromInvariant (Invariant _ pre bounds (PredTimed predpre predpost)) =
  concatMap locsFromExp pre <>  concatMap locsFromExp bounds
  <> locsFromExp predpre <> locsFromExp predpost

locsFromConstrInvariant :: TypedExplicit.Invariant -> [TypedExplicit.Location]
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

isLocalLoc :: StorageLocation t -> Bool
isLocalLoc (SLoc _ _ item) = isLocalItem item

isLocalItem :: TItem a k t -> Bool
isLocalItem (Item _ _ ref) = isLocalRef ref

isLocalRef :: Ref k t -> Bool
isLocalRef (SVar _ _ _) = True
isLocalRef (CVar _ _ _) = False
isLocalRef (SArray _ ref _ _) = isLocalRef ref
isLocalRef (SMapping _ ref _ _) = isLocalRef ref
isLocalRef (SField _ _ _ _) = False

isStorageLoc :: Location t -> Bool
isStorageLoc (Loc _ _ SStorage _) = True
isStorageLoc _ = False

partitionLocs :: [Location t] -> ([StorageLocation t], [CalldataLocation t])
partitionLocs locs = foldMap sepLoc locs
  where
    sepLoc :: Location t -> ([StorageLocation t], [CalldataLocation t])
    sepLoc (Loc typ s SStorage item) = ([SLoc typ s item],[])
    sepLoc (Loc typ s SCalldata item) = ([],[CLoc typ s item])

locsFromUpdate :: StorageUpdate t -> [Location t]
locsFromUpdate update = nub $ case update of
  (Update _ _ item e) -> locsFromItem SStorage item <> locsFromExp e

locsFromUpdateRHS :: StorageUpdate t -> [Location t]
locsFromUpdateRHS update = nub $ case update of
  (Update _ _ _ e) -> locsFromExp e

locFromUpdate :: StorageUpdate t -> StorageLocation t
locFromUpdate (Update typ s item _) = SLoc typ s item

locsFromItem :: SRefKind k -> TItem a k t -> [Location t]
locsFromItem k item = _Loc k item : concatMap locsFromTypedExp (ixsFromItem item)

locsFromTypedExp :: TypedExp t -> [Location t]
locsFromTypedExp (TExp _ _ e) = locsFromExp e

locsFromExp :: Exp a t -> [Location t]
locsFromExp = nub . go
  where
    go :: Exp a t -> [Location t]
    go e = case e of
      And _ a b   -> go a <> go b
      Or _ a b    -> go a <> go b
      Impl _ a b  -> go a <> go b
      Eq _ _ _ a b    -> go a <> go b
      LT _ a b    -> go a <> go b
      LEQ _ a b   -> go a <> go b
      GT _ a b    -> go a <> go b
      GEQ _ a b   -> go a <> go b
      NEq _ _ _ a b   -> go a <> go b
      Neg _ a     -> go a
      Add _ a b   -> go a <> go b
      Sub _ a b   -> go a <> go b
      Mul _ a b   -> go a <> go b
      Div _ a b   -> go a <> go b
      Mod _ a b   -> go a <> go b
      Exp _ a b   -> go a <> go b
      List _ l -> concatMap go l
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
      Create _ _ es -> concatMap locsFromTypedExp es
      ITE _ x y z -> go x <> go y <> go z
      VarRef _ _ k a -> locsFromItem k a

createsFromExp :: Exp a t -> [Id]
createsFromExp = nub . go
 where
   go :: Exp a t -> [Id]
   go e = case e of
     And _ a b   -> go a <> go b
     Or _ a b    -> go a <> go b
     Impl _ a b  -> go a <> go b
     Eq _ _ _ a b    -> go a <> go b
     LT _ a b    -> go a <> go b
     LEQ _ a b   -> go a <> go b
     GT _ a b    -> go a <> go b
     GEQ _ a b   -> go a <> go b
     NEq _ _ _ a b   -> go a <> go b
     Neg _ a     -> go a
     Add _ a b   -> go a <> go b
     Sub _ a b   -> go a <> go b
     Mul _ a b   -> go a <> go b
     Div _ a b   -> go a <> go b
     Mod _ a b   -> go a <> go b
     Exp _ a b   -> go a <> go b
     List _ l  -> concatMap go l
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
     Create _ f es -> [f] <> concatMap createsFromTypedExp es
     ITE _ x y z -> go x <> go y <> go z
     VarRef _ _ _ a -> createsFromItem a

createsFromItem :: TItem k a t -> [Id]
createsFromItem item = concatMap createsFromTypedExp (ixsFromItem item)

createsFromTypedExp :: TypedExp t -> [Id]
createsFromTypedExp (TExp _ _ e) = createsFromExp e

createsFromContract :: Contract t -> [Id]
createsFromContract (Contract constr behvs) =
  createsFromConstructor constr <> concatMap createsFromBehaviour behvs

createsFromConstructor :: Constructor t -> [Id]
createsFromConstructor (Constructor _ _ _ pre post inv initialStorage) = nub $
  concatMap createsFromExp pre
  <> concatMap createsFromExp post
  <> concatMap createsFromInvariant inv
  <> concatMap createsFromUpdate initialStorage

createsFromInvariant :: Invariant t -> [Id]
createsFromInvariant (Invariant _ pre bounds ipred) =
  concatMap createsFromExp pre <>  concatMap createsFromExp bounds <> createsFromInvariantPred ipred

createsFromInvariantPred :: InvariantPred t -> [Id]
createsFromInvariantPred (PredUntimed p) = createsFromExp p
createsFromInvariantPred (PredTimed pre post) = createsFromExp pre <> createsFromExp post

createsFromUpdate :: StorageUpdate t ->[Id]
createsFromUpdate update = nub $ case update of
  TypedExplicit.Update _ _ item e -> createsFromItem item <> createsFromExp e

createsFromBehaviour :: Behaviour t -> [Id]
createsFromBehaviour (Behaviour _ _ _ _ _ preconds postconds rewrites returns) = nub $
  concatMap createsFromExp preconds
  <> concatMap createsFromExp postconds
  <> concatMap createsFromUpdate rewrites
  <> maybe [] createsFromTypedExp returns


pointersFromContract :: Contract t -> [Id]
pointersFromContract (Contract constr behvs) =
  nub $ pointersFromConstructor constr <> concatMap pointersFromBehaviour behvs

pointersFromConstructor :: Constructor t -> [Id]
pointersFromConstructor (Constructor _ _ ptrs _ _ _ _) =
  map (\(PointsTo _ _ c) -> c) ptrs

pointersFromBehaviour :: Behaviour t -> [Id]
pointersFromBehaviour (Behaviour _ _ _ ptrs _ _ _ _ _) =
  map (\(PointsTo _ _ c) -> c) ptrs

ethEnvFromBehaviour :: Behaviour t -> [EthEnv]
ethEnvFromBehaviour (Behaviour _ _ _ _ preconds cases postconds rewrites returns) = nub $
  concatMap ethEnvFromExp preconds
  <> concatMap ethEnvFromExp cases
  <> concatMap ethEnvFromExp postconds
  <> concatMap ethEnvFromUpdate rewrites
  <> maybe [] ethEnvFromTypedExp returns

ethEnvFromConstructor :: TypedExplicit.Constructor -> [EthEnv]
ethEnvFromConstructor (TypedExplicit.Constructor _ _ _ pre post inv initialStorage) = nub $
  concatMap ethEnvFromExp pre
  <> concatMap ethEnvFromExp post
  <> concatMap ethEnvFromInvariant inv
  <> concatMap ethEnvFromUpdate initialStorage

ethEnvFromInvariant :: TypedExplicit.Invariant -> [EthEnv]
ethEnvFromInvariant (Invariant _ pre bounds invpred) =
  concatMap ethEnvFromExp pre <>  concatMap ethEnvFromExp bounds <> ethEnvFromInvariantPred invpred

ethEnvFromInvariantPred :: InvariantPred t -> [EthEnv]
ethEnvFromInvariantPred (PredUntimed p) = ethEnvFromExp p
ethEnvFromInvariantPred (PredTimed pre post) = ethEnvFromExp pre <> ethEnvFromExp post

ethEnvFromUpdate :: StorageUpdate t -> [EthEnv]
ethEnvFromUpdate rewrite = case rewrite of
  TypedExplicit.Update _ _ item e -> nub $ ethEnvFromItem item <> ethEnvFromExp e

ethEnvFromItem :: TItem k a t -> [EthEnv]
ethEnvFromItem = nub . concatMap ethEnvFromTypedExp . ixsFromItem

ethEnvFromTypedExp :: TypedExp t -> [EthEnv]
ethEnvFromTypedExp (TExp _ _ e) = ethEnvFromExp e

ethEnvFromExp :: Exp a t -> [EthEnv]
ethEnvFromExp = nub . go
  where
    go :: Exp a t -> [EthEnv]
    go e = case e of
      And   _ a b   -> go a <> go b
      Or    _ a b   -> go a <> go b
      Impl  _ a b   -> go a <> go b
      Eq    _ _ _ a b   -> go a <> go b
      LT    _ a b   -> go a <> go b
      LEQ   _ a b   -> go a <> go b
      GT    _ a b   -> go a <> go b
      GEQ   _ a b   -> go a <> go b
      NEq   _ _ _ a b   -> go a <> go b
      Neg   _ a     -> go a
      Add   _ a b   -> go a <> go b
      Sub   _ a b   -> go a <> go b
      Mul   _ a b   -> go a <> go b
      Div   _ a b   -> go a <> go b
      Mod   _ a b   -> go a <> go b
      Exp   _ a b   -> go a <> go b
      List _ l -> concatMap go l
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
      Create _ _ ixs -> concatMap ethEnvFromTypedExp ixs
      VarRef _ _ _ a -> ethEnvFromItem a

idFromItem :: TItem a k t -> Id
idFromItem (Item _ _ ref) = idFromRef ref

idFromRef :: Ref k t -> Id
idFromRef (SVar _ _ x) = x
idFromRef (CVar _ _ x) = x
idFromRef (SArray _ e _ _) = idFromRef e
idFromRef (SMapping _ e _ _) = idFromRef e
idFromRef (SField _ e _ _) = idFromRef e

idFromUpdate :: StorageUpdate t -> Id
idFromUpdate (TypedExplicit.Update _ _ item _) = idFromItem item

idFromLocation :: Location t -> Id
idFromLocation (Loc _ _ _ item) = idFromItem item

--ctorFromLocation :: Location t -> Id
--ctorFromLocation (Loc _ SStorage item) = ctorFromItem item

ctorFromItem :: TItem a 'Storage t -> Id
ctorFromItem (Item _ _ ref) = ctorFromRef ref

ctorFromRef :: Ref 'Storage t -> Id
ctorFromRef (SVar _ c _) = c
ctorFromRef (SArray _ e _ _) = ctorFromRef e
ctorFromRef (SMapping _ e _ _) = ctorFromRef e
ctorFromRef (SField _ _ c _) = c

-- Used to compare all identifiers in a location access
idsFromLocation :: StorageLocation t -> [String]
idsFromLocation (SLoc _ _ item) = idsFromItem item

idsFromItem :: TItem a k t -> [String]
idsFromItem (Item _ _ ref) = idsFromRef ref

idsFromRef :: Ref k t -> [String]
idsFromRef (SVar _ _ x) = [x]
idsFromRef (CVar _ _ x) = [x]
idsFromRef (SArray _ e _ _) = idsFromRef e
idsFromRef (SMapping _ e _ _) = idsFromRef e
idsFromRef (SField _ e _ f) = f : idsFromRef e

ixsFromItem :: TItem a k t -> [TypedExp t]
ixsFromItem (Item _ _ item) = ixsFromRef item

ixsFromSLocation :: StorageLocation t -> [TypedExp t]
ixsFromSLocation (SLoc _ _ item) = ixsFromItem item

ixsFromRef :: Ref k t -> [TypedExp t]
ixsFromRef (SVar _ _ _) = []
ixsFromRef (CVar _ _ _) = []
ixsFromRef (SArray _ ref _ ixs) = (fst <$> ixs) ++ ixsFromRef ref
ixsFromRef (SMapping _ ref _ ixs) = ixs ++ ixsFromRef ref
ixsFromRef (SField _ ref _ _) = ixsFromRef ref

ixsFromUpdate :: StorageUpdate t -> [TypedExp t]
ixsFromUpdate (TypedExplicit.Update _ _ item _) = ixsFromItem item

itemType :: TItem a k t -> ActType
itemType (Item t _ _) = actType t

isIndexed :: TItem a k t -> Bool
isIndexed item = isArray item || isMapping item

isArrayLoc :: Location t -> Bool
isArrayLoc (Loc _ _ _ item) = isArray item

isArray :: TItem a k t -> Bool
isArray (Item _ _ ref) = isArrayRef ref

isArrayRef :: Ref k t -> Bool
isArrayRef (SVar _ _ _) = False
isArrayRef (CVar _ _ _) = False
isArrayRef (SArray _ _ _ _) = True
isArrayRef (SMapping _ _ _ _) = False  -- may change in the future
isArrayRef (SField _ ref _ _) = isArrayRef ref

isMappingLoc :: Location t -> Bool
isMappingLoc (Loc _ _ _ item) = isMapping item

isMapping :: TItem a k t -> Bool
isMapping (Item _ _ ref) = isMappingRef ref

isMappingRef :: Ref k t -> Bool
isMappingRef (SVar _ _ _) = False
isMappingRef (CVar _ _ _) = False
isMappingRef (SArray _ _ _ _) = False  -- may change in the future
isMappingRef (SMapping _ _ _ _) = True
isMappingRef (SField _ ref _ _) = isMappingRef ref
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

  List p _ -> p

  -- bytestrings
  Cat p _ _ -> p
  Slice p _ _ _ -> p
  ByStr p _ -> p
  ByLit p _ -> p
  ByEnv p _ -> p
  -- contracts
  Create p _ _ -> p

  -- polymorphic
  Eq  p _ _ _ _ -> p
  NEq p _ _ _ _ -> p
  ITE p _ _ _ -> p
  VarRef p _ _ _ -> p

posnFromRef :: Ref a k -> Pn
posnFromRef (CVar p _ _) = p
posnFromRef (SVar p _ _) = p
posnFromRef (SArray p _ _ _) = p
posnFromRef (SMapping p _ _ _) = p
posnFromRef (SField p _ _ _) = p

-- | Given the shape of a nested list (outer to inner lengths)
-- returns an array of all indices
exprListIdcs :: NonEmpty.NonEmpty Int -> [[Int]]
exprListIdcs typ = map idx [0..(len - 1)]
  where
    -- The result of scanr is always non-empty
    (len NonEmpty.:| typeAcc) = NonEmpty.scanr (*) 1 typ
    idx e = zipWith (\ x1 x2 -> (e `div` x2) `mod` x1) (NonEmpty.toList typ) typeAcc
 
expandItem :: TItem a k t -> [TItem (Base a) k t]
expandItem (Item typ (PrimitiveType at) ref) = case flattenAbiType at of
  (ba, Just shape) -> case ref of
    SArray p r _ i -> maybe [] (\Refl -> (\i' -> Item btyp (PrimitiveType ba) $
      SArray p r (PrimitiveType ba) (i ++ (zip ((TExp SInteger Atomic . LitInt nowhere . fromIntegral) <$> i') $ NonEmpty.toList shape)) ) <$> exprListIdcs shape) $ testEquality typ btyp
    r -> maybe [] (\Refl -> (\i' -> Item btyp (PrimitiveType ba) $
      SArray nowhere r (PrimitiveType ba) (zip ((TExp SInteger Atomic . LitInt nowhere . fromIntegral) <$> i') $ NonEmpty.toList shape) ) <$> exprListIdcs shape) $ testEquality typ btyp

  (_, Nothing) -> [Item btyp (PrimitiveType at) ref]
  where
    btyp = fst $ flattenSType typ
expandItem (Item typ (ContractType at) ref) = [Item btyp (ContractType at) ref]
  where
    btyp = fst $ flattenSType typ

---- TODO: need to validate that expandItem gives the same order as expandListExpr
--expandListExpr :: SType (AArray a) -> Exp (AArray a) t -> (SType (Base (AArray a)), Shape (TypeShape a), [Exp (Base (AArray a)) t])
--expandListExpr t@(SSArray SInteger) (List _ l) = (fst $ flattenSType t, Atomic ,l)
--expandListExpr t@(SSArray SBoolean) (List _ l) = (fst $ flattenSType t, Atomic ,l)
--expandListExpr t@(SSArray SByteStr) (List _ l) = (fst $ flattenSType t, Atomic ,l)
--expandListExpr t@(SSArray s@(SSArray _)) (List _ l) = case fst $ flattenSType t of
--  SInteger -> (SInteger, Atomic , concatMap (snd . expandListExpr s) l)
--  _ -> undefined
---- TODO: Should pn stay the same?
--expandListExpr typ (VarRef pn t k item) = (fst $ flattenSType typ, Atomic , VarRef pn t k <$> expandItem item)
--expandListExpr typ (ITE pn tbool e1 e2) = (fst $ flattenSType typ, Atomic , (uncurry $ ITE pn tbool) <$> zip (snd $ snd $ expandListExpr typ e1) (snd $ snd $ expandListExpr typ e2))
--
--------------------------------------
-- * Extraction from untyped ASTs * --
--------------------------------------

nameFromStorage :: Untyped.Storage -> Id
nameFromStorage (Untyped.Update e _) = nameFromEntry e

nameFromEntry :: Entry -> Id
nameFromEntry (EVar _ x) = x
nameFromEntry (EIndexed _ e _) = nameFromEntry e
nameFromEntry (EField _ e _) = nameFromEntry e

nameFromBehv :: TypedExplicit.Behaviour -> Id
nameFromBehv (Behaviour _ _ (Interface ifaceName _) _ _ _ _ _ _) = ifaceName

getPosEntry :: Entry -> Pn
getPosEntry (EVar pn _) = pn
getPosEntry (EIndexed pn _ _) = pn
getPosEntry (EField pn _ _) = pn

getPosNL :: NestedList Pn a -> Pn
getPosNL (LeafList pn _) = pn
getPosNL (NodeList pn _) = pn

getPosn :: Expr -> Pn
getPosn expr = case expr of
    EAnd pn  _ _ -> pn
    EOr pn _ _ -> pn
    ENot pn _ -> pn
    EImpl pn _ _ -> pn
    EEq pn _ _ -> pn
    ENeq pn _ _ -> pn
    ELEQ pn _ _ -> pn
    ELT pn _ _ -> pn
    EGEQ pn _ _ -> pn
    EGT pn _ _ -> pn
    EAdd pn _ _ -> pn
    ESub pn _ _ -> pn
    EITE pn _ _ _ -> pn
    EMul pn _ _ -> pn
    EDiv pn _ _ -> pn
    EMod pn _ _ -> pn
    EExp pn _ _ -> pn
    ECreate pn _ _ -> pn
    EUTEntry e -> getPosEntry e
    EPreEntry e -> getPosEntry e
    EPostEntry e -> getPosEntry e
    EList pn _ -> pn
    ListConst e -> getPosn e
    ECat pn _ _ -> pn
    ESlice pn _ _ _ -> pn
    ENewaddr pn _ _ -> pn
    ENewaddr2 pn _ _ _ -> pn
    BYHash pn _ -> pn
    BYAbiE pn _ -> pn
    StringLit pn _ -> pn
    WildExp pn -> pn
    EnvExp pn _ -> pn
    IntLit pn _ -> pn
    BoolLit pn _ -> pn
    EInRange pn _ _ -> pn

posFromDef :: Mapping -> Pn
posFromDef (Mapping e _) = getPosn e

-- | Returns all the identifiers used in an expression,
-- as well all of the positions they're used in.
idFromRewrites :: Expr -> Map Id [Pn]
idFromRewrites e = case e of
  EAnd _ a b        -> idFromRewrites' [a,b]
  EOr _ a b         -> idFromRewrites' [a,b]
  ENot _ a          -> idFromRewrites a
  EImpl _ a b       -> idFromRewrites' [a,b]
  EEq _ a b         -> idFromRewrites' [a,b]
  ENeq _ a b        -> idFromRewrites' [a,b]
  ELEQ _ a b        -> idFromRewrites' [a,b]
  ELT _ a b         -> idFromRewrites' [a,b]
  EGEQ _ a b        -> idFromRewrites' [a,b]
  EGT _ a b         -> idFromRewrites' [a,b]
  EAdd _ a b        -> idFromRewrites' [a,b]
  ESub _ a b        -> idFromRewrites' [a,b]
  EITE _ a b c      -> idFromRewrites' [a,b,c]
  EMul _ a b        -> idFromRewrites' [a,b]
  EDiv _ a b        -> idFromRewrites' [a,b]
  EMod _ a b        -> idFromRewrites' [a,b]
  EExp _ a b        -> idFromRewrites' [a,b]
  EUTEntry en       -> idFromEntry en
  EPreEntry en      -> idFromEntry en
  EPostEntry en     -> idFromEntry en
  ECreate p x es    -> insertWith (<>) x [p] $ idFromRewrites' es
  EList _ l         -> idFromRewrites' l
  ListConst a       -> idFromRewrites a
  ECat _ a b        -> idFromRewrites' [a,b]
  ESlice _ a b c    -> idFromRewrites' [a,b,c]
  ENewaddr _ a b    -> idFromRewrites' [a,b]
  ENewaddr2 _ a b c -> idFromRewrites' [a,b,c]
  BYHash _ a        -> idFromRewrites a
  BYAbiE _ a        -> idFromRewrites a
  StringLit {}      -> empty
  WildExp {}        -> empty
  EnvExp {}         -> empty
  IntLit {}         -> empty
  BoolLit {}        -> empty
  EInRange _ _ a    -> idFromRewrites a
  where
    idFromRewrites' = unionsWith (<>) . fmap idFromRewrites

    idFromEntry :: Entry -> Map Id [Pn]
    idFromEntry (EVar p x) = singleton x [p]
    idFromEntry (EIndexed _ en xs) = unionWith (<>) (idFromEntry en) (idFromRewrites' xs)
    idFromEntry (EField _ en _) = idFromEntry en

-- | True iff the case is a wildcard.
isWild :: Case -> Bool
isWild (Case _ (WildExp _) _) = True
isWild _                      = False

bound :: AbiType -> Exp AInteger t -> Exp ABoolean t
bound typ e = And nowhere (LEQ nowhere (lowerBound typ) e) $ LEQ nowhere e (upperBound typ)

lowerBound :: forall t. AbiType -> Exp AInteger t
lowerBound (AbiIntType a) = IntMin nowhere a
-- todo: other negatives?
lowerBound _ = LitInt nowhere 0

-- todo, the rest
upperBound :: forall t. AbiType -> Exp AInteger t
upperBound (AbiUIntType  n) = UIntMax nowhere n
upperBound (AbiIntType   n) = IntMax nowhere n
upperBound AbiAddressType   = UIntMax nowhere 160
upperBound (AbiBytesType n) = UIntMax nowhere (8 * n)
upperBound typ = error $ "upperBound not implemented for " ++ show typ
