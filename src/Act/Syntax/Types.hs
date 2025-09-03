{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes, TypeApplications, PolyKinds #-}

{-|
Module      : Syntax.Types
Description : Types that represent Act types, and functions and patterns to go between them and Haskell's own types.
-}

module Act.Syntax.Types (module Act.Syntax.Types) where

import Data.Singletons
import Data.ByteString
import Data.List.NonEmpty
import qualified Data.List.NonEmpty as NonEmpty (singleton)
import Data.Type.Equality (TestEquality(..), (:~:)(..))
import EVM.ABI            as Act.Syntax.Types (AbiType(..))

import Act.Syntax.Untyped (ValueType(..))

-- | Types of Act expressions
data ActType where
  AInteger :: ActType
  ABoolean :: ActType
  AByteStr :: ActType
  AArray   :: ActType -> ActType

-- | Singleton runtime witness for Act types. Sometimes we need to examine type
-- tags at runtime. Tagging structures with this type will let us do that.
data SType (a :: ActType) where
  SInteger  :: SType AInteger
  SBoolean  :: SType ABoolean
  SByteStr  :: SType AByteStr
  SSArray   :: SType a -> SType (AArray a)
deriving instance Eq (SType a)

instance Show (SType a) where
  show = \case
    SInteger -> "int"
    SBoolean -> "bool"
    SByteStr -> "bytestring"
    SSArray a -> show a ++ " array"

type instance Sing = SType

instance TestEquality SType where
  testEquality SInteger SInteger = Just Refl
  testEquality SBoolean SBoolean = Just Refl
  testEquality SByteStr SByteStr = Just Refl
  testEquality (SSArray a) (SSArray b) = (\Refl -> Just Refl) =<< testEquality a b
  testEquality _ _ = Nothing


-- | Compare equality of two things parametrized by types which have singletons.
eqS :: forall (a :: ActType) (b :: ActType) f t. (SingI a, SingI b, Eq (f a t)) => f a t -> f b t -> Bool
eqS fa fb = maybe False (\Refl -> fa == fb) $ testEquality (sing @a) (sing @b)

-- | The same but when the higher-kinded type has two type arguments
eqS' :: forall (a :: ActType) (b :: ActType) f t t'. (SingI a, SingI b, Eq (f a t t')) => f a t t' -> f b t t' -> Bool
eqS' fa fb = maybe False (\Refl -> fa == fb) $ testEquality (sing @a) (sing @b)

-- Defines which singleton to retrieve when we only have the type, not the
-- actual singleton.
instance SingI 'AInteger where sing = SInteger
instance SingI 'ABoolean where sing = SBoolean
instance SingI 'AByteStr where sing = SByteStr
instance SingI a => SingI ('AArray a) where sing = SSArray (sing @a)

instance SingKind ActType where
  type Demote ActType = ActType

  fromSing SInteger = AInteger
  fromSing SBoolean = ABoolean
  fromSing SByteStr = AByteStr
  fromSing (SSArray a) = AArray $ fromSing a

  toSing AInteger = SomeSing SInteger
  toSing ABoolean = SomeSing SBoolean
  toSing AByteStr = SomeSing SByteStr
  toSing (AArray a) = case toSing a of
    SomeSing s -> SomeSing (SSArray s)


-- | Reflection of an Act type into a haskell type. Used to define the result
-- type of the evaluation function.
type family TypeOf a where
  TypeOf 'AInteger = Integer
  TypeOf 'ABoolean = Bool
  TypeOf 'AByteStr = ByteString
  TypeOf ('AArray a) = [TypeOf a]

-- Given a possibly nested ABI Array Type, returns the
-- elements' ABI type, as well as the size at each level
flattenArrayAbiType :: AbiType -> Maybe (AbiType, NonEmpty Int)
flattenArrayAbiType (AbiArrayType n t) = case flattenArrayAbiType t of
  Just (bt, li) -> Just (bt, n <| li)
  Nothing -> Just (t, pure n)
flattenArrayAbiType _ = Nothing

flattenAbiType :: AbiType -> (AbiType, Maybe (NonEmpty Int))
flattenAbiType (AbiArrayType n t) = case flattenAbiType t of
  (a, Nothing) -> (a, Just $ NonEmpty.singleton n)
  (a, l) -> (a, ((<|) n) <$> l)
flattenAbiType a = (a, Nothing)

-- experiment
--class HasBase (a :: Type) where
--  type family BaseOf a :: Type
type family Base (a :: ActType) :: ActType where
  Base (AArray a) = Base a
  Base AInteger = AInteger
  Base ABoolean = ABoolean
  Base AByteStr = AByteStr

--instance HasBase (SType (a :: ActType)) where
--  type instance BaseOf (SType (AArray a)) = BaseOf (SType a)
--  type instance BaseOf (SType (AArray a)) = BaseOf (SType a)

--flattenSType :: forall (a:: ActType) (b :: ActType). SType b ~ Base (SType a) => SType a -> (SType b, Maybe Int)
flattenSType :: SType a -> (SType (Base a), Maybe Int)
flattenSType (SSArray s') = case flattenSType s' of
  (s, Nothing) -> (s, Just 1)
  (s, Just n) -> (s, Just $ n+1)
flattenSType SInteger = (SInteger, Nothing)
flattenSType SBoolean = (SBoolean, Nothing)
flattenSType SByteStr = (SByteStr, Nothing)

fromAbiType :: AbiType -> ActType
fromAbiType (AbiUIntType _)     = AInteger
fromAbiType (AbiIntType  _)     = AInteger
fromAbiType AbiAddressType      = AInteger
fromAbiType AbiBoolType         = ABoolean
fromAbiType (AbiBytesType n)    = if n <= 32 then AInteger else AByteStr
fromAbiType AbiBytesDynamicType = AByteStr
fromAbiType AbiStringType       = AByteStr
fromAbiType (AbiArrayType _ a)  = AArray $ fromAbiType a
fromAbiType _ = error "Syntax.Types.actType: TODO"


someType :: ActType -> SomeType
someType AInteger = SomeType SInteger
someType ABoolean = SomeType SBoolean
someType AByteStr = SomeType SByteStr
someType (AArray a) = case someType a of
  (FromSome styp ) -> SomeType $ SSArray styp

actType :: SType s -> ActType
actType SInteger = AInteger
actType SBoolean = ABoolean
actType SByteStr = AByteStr
actType (SSArray a) = AArray $ actType a

fromValueType :: ValueType -> ActType
fromValueType (PrimitiveType t) = fromAbiType t
fromValueType (ContractType _) = AInteger

data SomeType where
  SomeType :: SingI a => SType a -> SomeType

-- | Pattern match on an 'SomeType' is if it were an 'SType'.
pattern FromSome :: () => (SingI a) => SType a -> SomeType
pattern FromSome t <- SomeType t
{-# COMPLETE FromSome #-}

-- | Pattern match on an 'AbiType' is if it were an 'SType'.
pattern FromAbi :: () => (SingI a) => SType a -> AbiType
pattern FromAbi t <- (someType . fromAbiType -> FromSome t)
{-# COMPLETE FromAbi #-}

-- | Pattern match on an 'ActType' is if it were an 'SType'.
pattern FromAct ::() => (SingI a) => SType a -> ActType
pattern FromAct t <- (someType -> FromSome t)
{-# COMPLETE FromAct #-}

-- | Pattern match on an 'ValueType' is if it were an 'SType'.
pattern FromVType :: () => (SingI a) => SType a -> ValueType
pattern FromVType t <- (someType . fromValueType -> FromSome t)
{-# COMPLETE FromVType #-}

-- | Helper pattern to retrieve the 'SingI' instances of the type
-- represented by an 'SType'.
pattern SType :: () => (SingI a) => SType a
pattern SType <- Sing
{-# COMPLETE SType #-}
