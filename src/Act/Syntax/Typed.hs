{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE InstanceSigs #-}

{-|
Module      : Syntax.Typed
Description : Typed AST datatype.

This module contains the datatype for the typed AST of an Act specification.
The typed AST is constructed during type checking. The type of each node is 
annotated with its Act type, so that it is well-typed by construction. 
The type of expressions is also annotated with a timing index: when the index
is `Timed` then all references to storage must be explicitly timed with `Pre` 
or `Post`. When the index is `Untimed` then expressions are not annotated with 
a time. After typechecking, in a separate pass, all expressions become `Timed`.

-}

module Act.Syntax.Typed (module Act.Syntax.Typed) where

import Control.Applicative (empty)
import Prelude hiding (GT, LT)

import Data.Aeson hiding (Array)
import Data.Aeson.Types hiding (Array)
import qualified Data.Aeson
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.List (genericTake,genericDrop)
import Data.Map.Strict (Map)
import Data.String (fromString)
import Data.Text (pack)
import Data.Vector (fromList)
import Data.Bifunctor
import Data.Singletons
import Data.Type.Equality (TestEquality(..), (:~:)(..))

-- Reexports

import Act.Lex            as Act.Syntax.Typed (nowhere)
import Act.Syntax.Types   as Act.Syntax.Typed
import Act.Syntax.Timing  as Act.Syntax.Typed
import Act.Syntax.Untyped as Act.Syntax.Typed (Interface(..), EthEnv(..), Arg(..), makeIface, ethEnv, IsPayable(..))

-- AST post typechecking
data Act t = Act StorageTyping [Contract t]
  deriving (Show, Eq)

data Contract t = Contract (Constructor t) [Behaviour t]
  deriving (Show, Eq)

-- For each contract, we store the type of a storage variables and the order in
-- which they are declared
type StorageTyping = Map Id (Map Id (ValueType, Integer))


-- | Represents a contract level invariant. The invariant is defined in the
-- context of the constructor, but must also be checked against each behaviour
-- in the contract, and thus may reference variables (i.e., constructor
-- arguments) that are not present in a given behavior so we additionally 
-- attach some constraints over the variables referenced by the predicate in 
-- the `_ipreconditions` field. The `_istoragebounds` field contains bound 
-- constraints for the storage variables referenced by the invariant predicate.
data Invariant t = Invariant
  { _icontract :: Id
  , _ipreconditions :: [Exp ABoolean t]
  , _istoragebounds :: [Exp ABoolean t] -- TODO check if this is indeed needed
  , _predicate :: InvariantPred t
  }
deriving instance Show (Invariant t)
deriving instance Eq (Invariant t)

-- | Invariant predicates are either a single predicate without explicit timing
-- or two predicates which explicitly reference the pre- and the post-state,
-- respectively.
data InvariantPred (t :: Timing) where
    PredUntimed :: Exp ABoolean Untimed -> InvariantPred Untimed
    PredTimed :: Exp ABoolean Timed -> Exp ABoolean Timed -> InvariantPred Timed
deriving instance Show (InvariantPred t)
deriving instance Eq (InvariantPred t)

-- type Case a t = (Exp ABoolean t, a)
type Cases a t = [(Exp ABoolean t, a)]

data Constructor t = Constructor
  { _cname :: Id
  , _cinterface :: Interface
  , _cisPayable :: IsPayable
  , _cpreconditions :: [Exp ABoolean t]
  , _ccases :: Cases [StorageUpdate t] t
  , _cpostconditions :: [Exp ABoolean t]
  , _invariants :: [Invariant t]
  } deriving (Show, Eq)
  
-- After typing each behavior may be split to multiple behaviors, one for each case branch.
-- In this case, only the `_caseconditions`, `_stateUpdates`, and `_returns` fields are different.
data Behaviour t = Behaviour
  { _name :: Id
  , _contract :: Id
  , _interface :: Interface
  , _isPayable :: IsPayable
  , _preconditions :: [Exp ABoolean t]  -- if preconditions are not satisfied execution is reverted
  , _cases :: Cases ([StorageUpdate t], Maybe (TypedExp Timed)) t
  , _postconditions :: [Exp ABoolean Timed]
  } deriving (Show, Eq)

data StorageUpdate (t :: Timing) where
  Update :: TValueType a -> Ref LHS t -> Exp a t -> StorageUpdate t
deriving instance Show (StorageUpdate t)

instance Eq (StorageUpdate t) where
  (==) :: StorageUpdate t -> StorageUpdate t -> Bool
  Update vt1@VType r1 e1 == Update vt2@VType r2 e2 = eqS'' vt1 vt2 && r1 == r2 && eqS e1 e2

-- | Distinguish the references that are updatable.
data RefKind = RHS | LHS
  deriving (Show, Eq)

data SRefKind (k :: RefKind) where
  SLHS  :: SRefKind LHS
  SRHS :: SRefKind RHS

type instance Sing = SRefKind

instance Show (SRefKind a) where
  show = \case
    SLHS -> "SLHS"
    SRHS -> "SRHS"

instance TestEquality SRefKind where
  testEquality SLHS SLHS = Just Refl
  testEquality SRHS SRHS = Just Refl
  testEquality _ _ = Nothing
  
-- | Helper pattern to retrieve the 'SingI' instances of the type represented by
-- an 'SKind'.
pattern SRefKind :: () => (SingI a) => SRefKind a
pattern SRefKind <- Sing
{-# COMPLETE SRefKind #-}

-- | Compare equality of two Items parametrized by different RefKinds.
eqKind' :: forall (a :: RefKind) (b :: RefKind) f t. (SingI a, SingI b, Eq (f a t)) => f a t -> f b t -> Bool
eqKind' fa fb = maybe False (\Refl -> fa == fb) $ testEquality (sing @a) (sing @b)

-- | Compare equality of two Items parametrized by different RefKinds.
eqKind :: forall (a :: RefKind) (b :: RefKind) f t t'. (SingI a, SingI b, Eq (f t a t')) => f t a t' -> f t b t' -> Bool
eqKind fa fb = maybe False (\Refl -> fa == fb) $ testEquality (sing @a) (sing @b)

-- | Compare equality of two Items parametrized by different ActTypes and RefKinds.
eqTypeKind :: forall (a :: ActType) (b :: ActType) (c :: RefKind)  (d :: RefKind) f t .
              (SingI a, SingI b, SingI c, SingI d, Eq (f a c t)) => f a c t -> f b d t -> Bool
eqTypeKind fa fb = maybe False (\Refl ->
                     maybe False (\Refl -> fa == fb)
                       $ testEquality (sing @c) (sing @d))
                         $ testEquality (sing @a) (sing @b)

-- | Variable References
data Ref (k :: RefKind) (t :: Timing) where
  CVar :: Pn -> ArgType -> Id -> Ref RHS t               -- Calldata variable  
  SVar :: Pn -> Time t -> Id -> Id -> Ref k t            -- Storage variable. First `Id` is the contract the var belongs to and the second the name.
  RArrIdx :: Pn -> Ref k t -> Exp AInteger t -> Int -> Ref k t
                                                         -- Array access. `Int` in indices list stores the corresponding index upper bound
  RMapIdx :: Pn -> TypedRef t -> TypedExp t -> Ref RHS t
  RField :: Pn -> Ref k t -> Id -> Id -> Ref k t         -- Field access (for accessing storage variables of contracts). Mapp
                                                         -- The first `Id` is the name of the contract that the field belongs to.
deriving instance Show (Ref k t)

instance Eq (Ref k t) where
  CVar _ at x         == CVar _ at' x'          = at == at' && x == x'
  SVar _ t c x        == SVar _ t' c' x'        = t == t' && c == c' && x == x'
  RArrIdx _ r t ix    == RArrIdx _ r' t' ix'    = r == r' && t == t' && ix == ix'
  RMapIdx _ r ix      == RMapIdx _ r' ix'       = r == r' &&  ix == ix'
  RField _ r c x      == RField _ r' c' x'      = r == r' && c == c' && x == x'
  _                   == _                      = False

data TypedRef (t :: Timing) where
  TRef :: TValueType a -> SRefKind k -> Ref k t -> TypedRef t
deriving instance Show (TypedRef t)

instance Eq (TypedRef t) where
  TRef vt1@VType SRefKind r1 == TRef vt2@VType SRefKind r2 = eqS'' vt1 vt2 && eqKind' r1 r2


-- | Expressions for which the return type is known.
data TypedExp t
  = forall (a :: ActType). SingI a => TExp (TValueType a) (Exp a t)
deriving instance Show (TypedExp t)

instance Eq (TypedExp t) where
  (==) :: TypedExp t -> TypedExp t -> Bool
  TExp vt1 e1 == TExp vt2 e2 = eqS'' vt1 vt2 && eqS e1 e2

--_TExp :: SingI a => Exp a t -> TypedExp t
--_TExp expr = TExp sing expr

-- | Expressions parametrized by a timing `t` and a type `a`. `t` can be either `Timed` or `Untimed`.
-- All storage entries within an `Exp a t` contain a value of type `Time t`.
-- If `t ~ Timed`, the only possible such values are `Pre, Post :: Time Timed`, so each storage entry
-- will refer to either the prestate or the poststate.
-- In `t ~ Untimed`, the only possible such value is `Neither :: Time Untimed`, so all storage entries
-- will not explicitly refer any particular state.
data Exp (a :: ActType) (t :: Timing) where
  -- booleans
  And  :: Pn -> Exp ABoolean t -> Exp ABoolean t -> Exp ABoolean t
  Or   :: Pn -> Exp ABoolean t -> Exp ABoolean t -> Exp ABoolean t
  Impl :: Pn -> Exp ABoolean t -> Exp ABoolean t -> Exp ABoolean t
  Neg :: Pn -> Exp ABoolean t -> Exp ABoolean t
  LT :: Pn -> Exp AInteger t -> Exp AInteger t -> Exp ABoolean t
  LEQ :: Pn -> Exp AInteger t -> Exp AInteger t -> Exp ABoolean t
  GEQ :: Pn -> Exp AInteger t -> Exp AInteger t -> Exp ABoolean t
  GT :: Pn -> Exp AInteger t -> Exp AInteger t -> Exp ABoolean t
  LitBool :: Pn -> Bool -> Exp ABoolean t
  -- integers
  Add :: Pn -> Exp AInteger t -> Exp AInteger t -> Exp AInteger t
  Sub :: Pn -> Exp AInteger t -> Exp AInteger t -> Exp AInteger t
  Mul :: Pn -> Exp AInteger t -> Exp AInteger t -> Exp AInteger t
  Div :: Pn -> Exp AInteger t -> Exp AInteger t -> Exp AInteger t
  Mod :: Pn -> Exp AInteger t -> Exp AInteger t -> Exp AInteger t
  Exp :: Pn -> Exp AInteger t -> Exp AInteger t -> Exp AInteger t
  LitInt :: Pn -> Integer -> Exp AInteger t
  IntEnv :: Pn -> EthEnv -> Exp AInteger t
  -- bounds
  IntMin :: Pn -> Int -> Exp AInteger t
  IntMax :: Pn -> Int -> Exp AInteger t
  UIntMin :: Pn -> Int -> Exp AInteger t
  UIntMax :: Pn -> Int -> Exp AInteger t
  InRange :: Pn -> TValueType AInteger -> Exp AInteger t -> Exp ABoolean t
  -- bytestrings
  Cat :: Pn -> Exp AByteStr t -> Exp AByteStr t -> Exp AByteStr t
  Slice :: Pn -> Exp AByteStr t -> Exp AInteger t -> Exp AInteger t -> Exp AByteStr t
  ByStr :: Pn -> String -> Exp AByteStr t
  ByLit :: Pn -> ByteString -> Exp AByteStr t
  ByEnv :: Pn -> EthEnv -> Exp AByteStr t

  Array :: Pn -> [Exp a t] -> Exp (AArray a) t
  -- contracts
  Create   :: Pn -> Id -> [TypedExp t] -> Maybe (Exp AInteger t) -> Exp AContract t
  -- polymorphic
  Eq  :: Pn -> TValueType a -> Exp a t -> Exp a t -> Exp ABoolean t
  NEq :: Pn -> TValueType a -> Exp a t -> Exp a t -> Exp ABoolean t
  ITE :: Pn -> Exp ABoolean t -> Exp a t -> Exp a t -> Exp a t
  -- variable references
  VarRef :: Pn -> TValueType a -> Ref RHS t -> Exp a t
  -- address of contract
  Address :: Pn -> Id -> Exp AContract t -> Exp AInteger t
  -- mappings
  Mapping :: Pn -> TValueType a -> TValueType b ->  [(Exp a t, Exp b t)] -> Exp AMapping t
  MappingUpd :: Pn -> Ref LHS t -> TValueType a -> TValueType b ->  [(Exp a t, Exp b t)] -> Exp AMapping t
deriving instance Show (Exp a t)


-- Equality modulo source file position.
instance Eq (Exp a t) where
  (==) :: Exp a t -> Exp a t -> Bool
  And _ a b == And _ c d = a == c && b == d
  Or _ a b == Or _ c d = a == c && b == d
  Impl _ a b == Impl _ c d = a == c && b == d
  Neg _ a == Neg _ b = a == b
  LT _ a b == LT _ c d = a == c && b == d
  LEQ _ a b == LEQ _ c d = a == c && b == d
  GEQ _ a b == GEQ _ c d = a == c && b == d
  GT _ a b == GT _ c d = a == c && b == d
  LitBool _ a == LitBool _ b = a == b

  Add _ a b == Add _ c d = a == c && b == d
  Sub _ a b == Sub _ c d = a == c && b == d
  Mul _ a b == Mul _ c d = a == c && b == d
  Div _ a b == Div _ c d = a == c && b == d
  Mod _ a b == Mod _ c d = a == c && b == d
  Exp _ a b == Exp _ c d = a == c && b == d
  LitInt _ a == LitInt _ b = a == b
  IntEnv _ a == IntEnv _ b = a == b

  IntMin _ a == IntMin _ b = a == b
  IntMax _ a == IntMax _ b = a == b
  UIntMin _ a == UIntMin _ b = a == b
  UIntMax _ a == UIntMax _ b = a == b
  InRange _ a b == InRange _ c d  = a == c && b == d

  Cat _ a b == Cat _ c d = a == c && b == d
  Slice _ a b c == Slice _ d e f = a == d && b == e && c == f
  ByStr _ a == ByStr _ b = a == b
  ByLit _ a == ByLit _ b = a == b
  ByEnv _ a == ByEnv _ b = a == b

  Eq _ vt1@VType a b == Eq _ vt2@VType c d = eqS'' vt1 vt2 && eqS a c && eqS b d
  NEq _ vt1@VType a b == NEq _ vt2@VType c d = eqS'' vt1 vt2 && eqS a c && eqS b d

  ITE _ a b c == ITE _ d e f = a == d && b == e && c == f
  VarRef _ a t == VarRef _ b u = a == b && t == u
  Create _ a b c == Create _ d e f = a == d && b == e && c == f
  Array _ a == Array _ b = a == b
  Address _ _ a == Address _ _ b = a == b
  Mapping _ (vt1@VType :: TValueType a1) (vt2@VType :: TValueType b1) m == Mapping _ (vt3@VType :: TValueType a2) (vt4@VType :: TValueType b2) m' = 
    (testEquality (sing @a1) (sing @a2) >>= \Refl ->
     testEquality (sing @b1) (sing @b2) >>= \Refl ->
     pure $ m == m' && vt1 == vt3 && vt2 == vt4) == Just True
  MappingUpd _ r (vt1@VType :: TValueType a1) (vt2@VType :: TValueType b1) m == MappingUpd _ r' (vt3@VType :: TValueType a2) (vt4@VType :: TValueType b2) m' = 
    r == r' &&
    (testEquality (sing @a1) (sing @a2) >>= \Refl ->
     testEquality (sing @b1) (sing @b2) >>= \Refl ->
     pure $ m == m' && vt1 == vt3 && vt2 == vt4) == Just True
  _ == _ = False


instance Semigroup (Exp ABoolean t) where
  a <> b = And nowhere a b

instance Monoid (Exp ABoolean t) where
  mempty = LitBool nowhere True

instance Timable TypedExp where
  setTime :: When -> TypedExp Untimed -> TypedExp Timed
  setTime time (TExp t expr) = TExp t $ setTime time expr

instance Timable (Exp a) where
  setTime :: When -> Exp a Untimed -> Exp a Timed
  setTime time expr = case expr of
    -- booleans
    And p x y -> And p (go x) (go y)
    Or   p x y -> Or p (go x) (go y)
    Impl p x y -> Impl p (go x) (go y)
    Neg p x -> Neg p (go x)
    LT p x y -> LT p (go x) (go y)
    LEQ p x y -> LEQ p (go x) (go y)
    GEQ p x y -> GEQ p (go x) (go y)
    GT p x y -> GT p (go x) (go y)
    LitBool p x -> LitBool p x
    -- integers
    Add p x y -> Add p (go x) (go y)
    Sub p x y -> Sub p (go x) (go y)
    Mul p x y -> Mul p (go x) (go y)
    Div p x y -> Div p (go x) (go y)
    Mod p x y -> Mod p (go x) (go y)
    Exp p x y -> Exp p (go x) (go y)
    LitInt p x -> LitInt p x
    IntEnv p x -> IntEnv p x
    -- bounds
    IntMin p x -> IntMin p x
    IntMax p x -> IntMax p x
    UIntMin p x -> UIntMin p x
    UIntMax p x -> UIntMax p x
    InRange p b e -> InRange p b (go e)

    Array p l -> Array p $ go <$> l

    -- bytestrings
    Cat p x y -> Cat p (go x) (go y)
    Slice p x y z -> Slice p (go x) (go y) (go z)
    ByStr p x -> ByStr p x
    ByLit p x -> ByLit p x
    ByEnv p x -> ByEnv p x
    -- contracts
    Create p x y z -> Create p x (go <$> y) (go <$> z)

    -- polymorphic
    Eq  p s x y -> Eq p s (go x) (go y)
    NEq p s x y -> NEq p s (go x) (go y)
    ITE p x y z -> ITE p (go x) (go y) (go z)
    VarRef p vt item -> VarRef p vt (go item)
    Address p c e -> Address p c (go e)
    -- mappings
    Mapping p kt vt kvs -> Mapping p kt vt (bimap go go <$> kvs)
    MappingUpd p r kt vt kvs -> MappingUpd p (go r) kt vt (bimap go go <$> kvs)
    where
      go :: Timable c => c Untimed -> c Timed
      go = setTime time


instance Timable TypedRef where
   setTime :: When -> TypedRef Untimed -> TypedRef Timed
   setTime time (TRef t k ref) = TRef t k $ setTime time ref

instance Timable (Ref k) where
  setTime :: When -> Ref k Untimed -> Ref k Timed
  setTime time (RMapIdx p e ix) = RMapIdx p (setTime time e) (setTime time ix)
  setTime time (RArrIdx p e ix n) = RArrIdx p (setTime time e) (setTime time ix) n
  setTime time (RField p e c x) = RField p (setTime time e) c x
  setTime time (SVar p _ c ref) = SVar p time c ref
  setTime _ (CVar p at ref) = CVar p at ref


------------------------
-- * JSON instances * --
------------------------

-- TODO dual instances are ugly! But at least it works for now.
-- It was difficult to construct a function with type:
-- `InvPredicate t -> Either (Exp Bool Timed,Exp Bool Timed) (Exp Bool Untimed)`
instance ToJSON (Act t) where
  toJSON (Act storages contracts) = object [ "kind" .= String "Act"
                                           , "store" .= storeJSON storages
                                           , "contracts" .= toJSON contracts ]

instance ToJSON (Contract t) where
  toJSON (Contract ctor behv) = object [ "kind" .= String "Contract"
                                       , "constructor" .= toJSON ctor
                                       , "behaviours" .= toJSON behv ]

storeJSON :: StorageTyping -> Value
storeJSON storages = object [ "kind" .= String "Storages"
                            , "storages" .= toJSON storages]

instance ToJSON (Constructor t) where
  toJSON Constructor{..} = object [ "kind" .= String "Constructor"
                                  , "contract" .= _cname
                                  , "interface" .= toJSON _cinterface
                                  , "preConditions" .= toJSON _cpreconditions
                                  , "postConditions" .= toJSON _cpostconditions
                                  , "invariants" .= listValue toJSON _invariants
                                  , "cases" .= toJSON _ccases  ]

instance ToJSON (Behaviour t) where
  toJSON Behaviour{..} = object [ "kind" .= String "Behaviour"
                                , "name" .= _name
                                , "contract" .= _contract
                                , "interface" .= toJSON _interface
                                , "preConditions" .= toJSON _preconditions
                                , "cases" .= toJSON _cases
                                , "postConditions" .= toJSON _postconditions ]

instance ToJSON Interface where
  toJSON (Interface x decls) = object [ "kind" .= String "Interface"
                                      , "id" .=  pack (show x)
                                      , "args" .= toJSON decls
                                      ]

instance ToJSON Arg where
  toJSON (Arg abitype x) = object [ "kind" .= String "Declaration"
                                   , "id" .= pack (show x)
                                   , "abitype" .= toJSON abitype
                                   ]

instance ToJSON (Invariant t) where
  toJSON Invariant{..} = object [ "kind" .= String "Invariant"
                                , "predicate" .= toJSON _predicate
                                , "preconditions" .= toJSON _ipreconditions
                                , "storagebounds" .= toJSON _istoragebounds
                                , "contract" .= _icontract ]

instance ToJSON (InvariantPred t) where
  toJSON (PredUntimed ipred) = object [ "kind" .= String "PredUntimed"
                                      , "predicate" .= toJSON ipred ]
  toJSON (PredTimed predpre predpost) = object [ "kind" .= String "PredUntimed"
                                               , "prefpredicate" .= toJSON predpre
                                               , "prefpredicate" .= toJSON predpost ]

instance ToJSON (StorageUpdate t) where
  toJSON (Update _ a b) = object [ "location" .= toJSON a ,"value" .= toJSON b ]

instance ToJSON (TypedRef t) where
  toJSON (TRef t k r) = object [ "ref" .= toJSON r
                               , "type" .=  show t
                               , "kind" .=  show k
                               ]

instance ToJSON (Ref k t) where
  toJSON (SVar _ t c x) = object [ "kind" .= pack "SVar"
                                 , "svar" .=  pack x
                                 , "time" .=  pack (show t)
                                 , "contract" .= pack c ]
  toJSON (CVar _ at x) = object [ "kind" .= pack "Var"
                                , "var" .=  pack x
                                , "abitype" .=  toJSON at ]
  toJSON (RArrIdx _ e x _) = array e x
  toJSON (RMapIdx _ e x) = mapping e x
  toJSON (RField _ e c x) = field e c x

array :: (ToJSON a1, ToJSON a2) => a1 -> a2 -> Value
array a b = object [ "kind"      .= pack "Array"
                   , "indexes"   .= toJSON b
                   , "reference" .= toJSON a]

mapping :: (ToJSON a1, ToJSON a2) => a1 -> a2 -> Value
mapping a b = object [ "kind"      .= pack "Mapping"
                     , "indexes"   .= toJSON b
                     , "reference" .= toJSON a]

field :: (ToJSON a1) => a1 -> Id -> Id -> Value
field a c x = object [ "kind"      .= pack "Field"
                     , "field"     .= pack x
                     , "contract"  .= pack c
                     , "reference" .= toJSON a
                     ]


instance ToJSON (TypedExp t) where
  toJSON (TExp typ a) = object [ "kind"       .= pack "TypedExpr"
                                 , "type"       .= pack (show typ)
                                 , "expression" .= toJSON a ]

instance ToJSON (Exp a t) where
  toJSON (Add _ a b) = symbol "+" a b
  toJSON (Sub _ a b) = symbol "-" a b
  toJSON (Exp _ a b) = symbol "^" a b
  toJSON (Mul _ a b) = symbol "*" a b
  toJSON (Div _ a b) = symbol "/" a b
  toJSON (LitInt _ a) = object [ "literal" .= pack (show a)
                               , "type" .= pack "int" ]
  toJSON (IntMin _ a) = object [ "literal" .= pack (show $ intmin a)
                               , "type" .= pack "int" ]
  toJSON (IntMax _ a) = object [ "literal" .= pack (show $ intmax a)
                               , "type" .= pack "int" ]
  toJSON (UIntMin _ a) = object [ "literal" .= pack (show $ uintmin a)
                                , "type" .= pack "int" ]
  toJSON (UIntMax _ a) = object [ "literal" .= pack (show $ uintmax a)
                                , "type" .= pack "int" ]
  toJSON (InRange _ a b) = object [ "symbol"   .= pack "inrange"
                                  , "arity"    .= Data.Aeson.Types.Number 2
                                  , "args"     .= Data.Aeson.Array (fromList [toJSON a, toJSON b]) ]
  toJSON (IntEnv _ a) = object [ "ethEnv" .= pack (show a)
                               , "type" .= pack "int" ]
  toJSON (ITE _ a b c) = object [ "symbol"   .= pack "ite"
                                , "arity"    .= Data.Aeson.Types.Number 3
                                , "args"     .= Data.Aeson.Array (fromList [toJSON a, toJSON b, toJSON c]) ]
  toJSON (And _ a b)  = symbol "and" a b
  toJSON (Or _ a b)   = symbol "or" a b
  toJSON (LT _ a b)   = symbol "<" a b
  toJSON (GT _ a b)   = symbol ">" a b
  toJSON (Impl _ a b) = symbol "=>" a b
  toJSON (NEq _ _ a b)  = symbol "=/=" a b
  toJSON (Eq _ _ a b)   = symbol "==" a b
  toJSON (LEQ _ a b)  = symbol "<=" a b
  toJSON (GEQ _ a b)  = symbol ">=" a b
  toJSON (LitBool _ a) = object [ "literal" .= pack (show a)
                                , "type" .= pack "bool" ]
  toJSON (Neg _ a) = object [ "symbol"   .= pack "not"
                            , "arity"    .= Data.Aeson.Types.Number 1
                            , "args"     .= Data.Aeson.Array (fromList [toJSON a]) ]

  toJSON (Cat _ a b) = symbol "cat" a b
  toJSON (Slice _ s a b) = object [ "symbol" .= pack "slice"
                                  , "arity"  .= Data.Aeson.Types.Number 3
                                  , "args"   .= Data.Aeson.Array (fromList [toJSON s, toJSON a, toJSON b]) ]
  toJSON (ByStr _ a) = object [ "bytestring" .= toJSON a
                              , "type" .= pack "bool" ]
  toJSON (ByLit _ a) = object [ "literal" .= pack (show a)
                              , "type" .= pack "bytestring" ]
  toJSON (ByEnv _ a) = object [ "ethEnv" .= pack (show a)
                              , "type" .= pack "bytestring" ]
  toJSON (VarRef _ t a) = object [ "var"  .= toJSON a
                                 , "timing" .= show t ]
  toJSON (Create _ f xs v) = object [ "symbol" .= pack "create"
                                    , "arity"  .= Data.Aeson.Types.Number (fromIntegral $ length xs)
                                    , "args"   .= Data.Aeson.Array (fromList [object [ "fun" .=  String (pack f) ], toJSON xs]) 
                                    , "value"  .= toJSON v ]
  toJSON (Array _ l) = object [ "symbol" .= pack "[]"
                              , "arity" .= Data.Aeson.Types.Number (fromIntegral $ length l)
                              , "args" .= Data.Aeson.Array (fromList (map toJSON l)) ]
  toJSON (Address _ _ x) = object [ "symbol" .= pack "addr"
                                , "arity" .= Data.Aeson.Types.Number 1
                                , "arg" .= toJSON x ]
  toJSON (Mapping _ kt vt kvs) = object [ "symbol" .= pack "mapping"
                                        , "keyType" .= show kt
                                        , "valueType" .= show vt
                                        , "entries" .= toJSON kvs ]
  toJSON (MappingUpd _ r kt vt kvs) = object [ "symbol" .= pack "mappingUpd"
                                             , "ref" .= toJSON r
                                             , "keyType" .= show kt
                                             , "valueType" .= show vt
                                             , "entries" .= toJSON kvs ]

  toJSON v = error $ "todo: json ast for: " <> show v



symbol :: (ToJSON a1, ToJSON a2) => String -> a1 -> a2 -> Value
symbol s a b = object [ "symbol"   .= pack s
                      , "arity"    .= Data.Aeson.Types.Number 2
                      , "args"     .= Data.Aeson.Array (fromList [toJSON a, toJSON b]) ]

-- | Simplifies concrete expressions into literals.
-- Returns `Nothing` if the expression contains symbols.
eval :: Exp a t -> Maybe (TypeOf a)
eval e = case e of
  And  _ a b    -> [a' && b' | a' <- eval a, b' <- eval b]
  Or   _ a b    -> [a' || b' | a' <- eval a, b' <- eval b]
  Impl _ a b    -> [a' <= b' | a' <- eval a, b' <- eval b]
  Neg  _ a      -> not <$> eval a
  LT   _ a b    -> [a' <  b' | a' <- eval a, b' <- eval b]
  LEQ  _ a b    -> [a' <= b' | a' <- eval a, b' <- eval b]
  GT   _ a b    -> [a' >  b' | a' <- eval a, b' <- eval b]
  GEQ  _ a b    -> [a' >= b' | a' <- eval a, b' <- eval b]
  LitBool _ a   -> pure a

  Add _ a b     -> [a' + b'     | a' <- eval a, b' <- eval b]
  Sub _ a b     -> [a' - b'     | a' <- eval a, b' <- eval b]
  Mul _ a b     -> [a' * b'     | a' <- eval a, b' <- eval b]
  Div _ a b     -> [a' `div` b' | a' <- eval a, b' <- eval b]
  Mod _ a b     -> [a' `mod` b' | a' <- eval a, b' <- eval b]
  Exp _ a b     -> [a' ^ b'     | a' <- eval a, b' <- eval b]
  LitInt  _ a   -> pure a
  IntMin  _ a   -> pure $ intmin  a
  IntMax  _ a   -> pure $ intmax  a
  UIntMin _ a   -> pure $ uintmin a
  UIntMax _ a   -> pure $ uintmax a
  InRange _ _ _ -> error "TODO eval in range"

  Cat _ s t     -> [s' <> t' | s' <- eval s, t' <- eval t]
  Slice _ s a b -> [BS.pack . genericDrop a' . genericTake b' $ s'
                            | s' <- BS.unpack <$> eval s
                            , a' <- eval a
                            , b' <- eval b]
  ByStr _ s     -> pure . fromString $ s
  ByLit _ s     -> pure s

  -- TODO better way to write these?
  Eq _ (TInteger _ _) x y -> [ x' == y' | x' <- eval x, y' <- eval y]
  Eq _ TBoolean x y -> [ x' == y' | x' <- eval x, y' <- eval y]
  Eq _ TByteStr x y -> [ x' == y' | x' <- eval x, y' <- eval y]

  NEq _ (TInteger _ _) x y -> [ x' /= y' | x' <- eval x, y' <- eval y]
  NEq _ TBoolean x y -> [ x' /= y' | x' <- eval x, y' <- eval y]
  NEq _ TByteStr x y -> [ x' /= y' | x' <- eval x, y' <- eval y]
  ITE _ a b c   -> eval a >>= \cond -> if cond then eval b else eval c

  Array _ l -> mapM eval l

  Create _ _ _ _ -> error "eval of contracts not supported"
  Address _ _ _ -> error "eval of contracts not supported"
  Mapping _ _ _ _ -> error "eval of mappings not supported"
  MappingUpd _ _ _ _ _ -> error "eval of mapping updates not supported"
  _              -> empty

intmin :: Int -> Integer
intmin a = negate $ 2 ^ (a - 1)

intmax :: Int -> Integer
intmax a = 2 ^ (a - 1) - 1

uintmin :: Int -> Integer
uintmin _ = 0

uintmax :: Int -> Integer
uintmax a = 2 ^ a - 1

_Var :: SingI a => TValueType a -> Id -> Exp a Timed
_Var vt x = VarRef nowhere vt (CVar nowhere (toArgType vt) x)

-- _Array :: SingI a => TValueType a -> Id -> [(TypedExp Timed, Int)] -> Exp a Timed
-- _Array vt x ix = VarRef nowhere vt SRHS (RArrIdx nowhere (CVar nowhere (toArgType vt) x) (fromAbiType (toAbiType vt)) ix)
