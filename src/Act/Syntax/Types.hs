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
{-# LANGUAGE RankNTypes, TypeApplications, PolyKinds #-}

{-|
Module      : Syntax.Types
Description : Types that represent Act types, and functions and patterns to go between them and Haskell's own types.
-}

module Act.Syntax.Types (module Act.Syntax.Types) where

import Data.Maybe (isNothing)
import Data.Singletons
import Data.ByteString hiding (concatMap, singleton, reverse)
import Data.List.NonEmpty hiding (reverse)
import qualified Data.List.NonEmpty as NonEmpty (singleton, toList)
import Data.Type.Equality (TestEquality(..), (:~:)(..))
import EVM.ABI            as Act.Syntax.Types (AbiType(..))

import Act.Syntax.Untyped (ValueType(..))

-- | Types of Act expressions
data ActType where
  AInteger  :: ActType
  ABoolean  :: ActType
  AByteStr  :: ActType
  AContract :: ActType
  AArray    :: ActType -> ActType

-- | Singleton runtime witness for Act types. Sometimes we need to examine type
-- tags at runtime. Tagging structures with this type will let us do that.
data SType (a :: ActType) where
  SInteger  :: SType AInteger
  SBoolean  :: SType ABoolean
  SByteStr  :: SType AByteStr
  SContract :: SType AContract
  SSArray   :: SType a -> SType (AArray a)
deriving instance Eq (SType a)

instance Show (SType a) where
  show = \case
    SInteger -> "int"
    SBoolean -> "bool"
    SByteStr -> "bytestring"
    SContract -> "contract"
    SSArray a -> show a ++ " array"

type instance Sing = SType

instance TestEquality SType where
  testEquality SInteger SInteger = Just Refl
  testEquality SBoolean SBoolean = Just Refl
  testEquality SByteStr SByteStr = Just Refl
  testEquality SContract SContract = Just Refl
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
instance SingI 'AContract where sing = SContract
instance SingI a => SingI ('AArray a) where sing = SSArray (sing @a)

-- | Extracts the base type from an array ActType or returns the type itself
-- for non-array types. Used when expanding an array expression into
-- expressions of its elements.
type family Base (a :: ActType) :: ActType where
  Base (AArray a) = Base a
  Base AInteger = AInteger
  Base ABoolean = ABoolean
  Base AByteStr = AByteStr
  Base AContract = AContract

flattenSType :: SType a -> SType (Base a)
flattenSType (SSArray s') = flattenSType s'
flattenSType SInteger = SInteger
flattenSType SBoolean = SBoolean
flattenSType SByteStr = SByteStr
flattenSType SContract = SContract

-- | Determines whether an ActType is atomic or can hold a shape.
-- Used with the 'Shape' datatype to prohibit discrepancies between
-- 'SType' parameters and the possible shape value.
type family ActShape (a :: ActType) :: AShape where
  ActShape 'AInteger = 'AAtomic
  ActShape 'ABoolean = 'AAtomic
  ActShape 'AByteStr = 'AAtomic
  ActShape 'AContract = 'AAtomic
  ActShape ('AArray a) = 'AShaped

-- | Determines atomicity or not for 'Shape' datatype,
-- used as promoted constructors.
data AShape = AAtomic | AShaped

-- | Shape of an array expression. Either atomic or a list
-- of the array lengths at each level (outer to inner).
data Shape (a :: AShape) where
  Atomic :: Shape 'AAtomic
  Shaped :: NonEmpty Int -> Shape 'AShaped
deriving instance Eq (Shape a)

instance Show (Shape a) where
  show Atomic = "Atomic"
  show (Shaped l) = concatMap (show . singleton) (reverse $ NonEmpty.toList l)

eqShape :: Shape a -> Shape b -> Bool
eqShape Atomic Atomic = True
eqShape (Shaped s1) (Shaped s2) | s1 == s2 = True
eqShape _ _ = False

shapeFromVT :: SType a -> ValueType -> Shape (ActShape a)
shapeFromVT SContract (ContractType _) = Atomic
shapeFromVT SInteger (ContractType _) = error "Internal Error: shapeFromVT: SInteger ContractType"
shapeFromVT SBoolean (ContractType _) = error "Internal Error: shapeFromVT: SBoolean ContractType"
shapeFromVT SByteStr (ContractType _) = error "Internal Error: shapeFromVT: SByteStr ContractType"
shapeFromVT (SSArray _) (ContractType _) = error "Internal Error: shapeFromVT: SSArray ContractType"
shapeFromVT SInteger (PrimitiveType a) | isNothing $ flattenArrayAbiType a = Atomic
shapeFromVT SBoolean (PrimitiveType a) | isNothing $ flattenArrayAbiType a = Atomic
shapeFromVT SByteStr (PrimitiveType a) | isNothing $ flattenArrayAbiType a = Atomic
shapeFromVT SContract (PrimitiveType a) | isNothing $ flattenArrayAbiType a = Atomic -- ??
shapeFromVT (SSArray _) (PrimitiveType a) =
  maybe (error "Internal Error: shapeFromVT: expected an array ABI Type") (Shaped . snd) $ flattenArrayAbiType a
shapeFromVT _ (PrimitiveType _) = error "Internal Error: shapeFromVT: expected a non-array ABI Type"

-- | Reflection of an Act type into a haskell type. Used to define the result
-- type of the evaluation function.
type family TypeOf a where
  TypeOf 'AInteger = Integer
  TypeOf 'ABoolean = Bool
  TypeOf 'AByteStr = ByteString
  TypeOf 'AContract = Integer
  TypeOf ('AArray a) = [TypeOf a]

-- Given a possibly nested ABI Array Type, returns the
-- elements' ABI type, as well as the size at each level.
flattenArrayAbiType :: AbiType -> Maybe (AbiType, NonEmpty Int)
flattenArrayAbiType at = case flattenAbiType at of
  (at', ms) -> (,) at' <$> ms

flattenAbiType :: AbiType -> (AbiType, Maybe (NonEmpty Int))
flattenAbiType (AbiArrayType n t) = case flattenAbiType t of
  (a, Nothing) -> (a, Just $ NonEmpty.singleton n)
  (a, l) -> (a, ((<|) n) <$> l)
flattenAbiType a = (a, Nothing)


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
someType AContract = SomeType SContract
someType (AArray a) = case someType a of
  (FromSome styp ) -> SomeType $ SSArray styp

actType :: SType s -> ActType
actType SInteger = AInteger
actType SBoolean = ABoolean
actType SByteStr = AByteStr
actType SContract = AContract
actType (SSArray a) = AArray $ actType a

fromValueType :: ValueType -> ActType
fromValueType (PrimitiveType t) = fromAbiType t
fromValueType (ContractType _) = AContract

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
