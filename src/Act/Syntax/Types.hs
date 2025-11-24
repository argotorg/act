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

import Data.Singletons
import qualified Data.Vector as V
import Data.ByteString hiding (concatMap, singleton, reverse, zipWith)
import Data.List.NonEmpty hiding (reverse, zipWith)
import qualified Data.List.NonEmpty as NonEmpty (singleton)
import Data.Type.Equality (TestEquality(..), (:~:)(..))
import EVM.ABI            as Act.Syntax.Types (AbiType(..))
import Data.Kind (Constraint)

-- | Types of Act expressions
data ActType where
  AInteger   :: ActType
  ABoolean   :: ActType
  AByteStr   :: ActType
  AStruct    :: ActType
  AArray     :: ActType -> ActType
  AContract  :: ActType

-- | Singleton runtime witness for Act types. Sometimes we need to examine type
-- tags at runtime. Tagging structures with this type will let us do that.
data SType (a :: ActType) where
  SInteger  :: SType AInteger
  SBoolean  :: SType ABoolean
  SByteStr  :: SType AByteStr
  SStruct   :: SType AStruct
  SSArray   :: SType a -> SType (AArray a)
  SContract :: SType AContract
deriving instance Eq (SType a)

instance Show (SType a) where
  show = \case
    SInteger -> "int"
    SBoolean -> "bool"
    SByteStr -> "bytestring"
    SStruct  -> "struct"
    SSArray a -> show a ++ " array"
    SContract -> "contract"

type instance Sing = SType

instance TestEquality SType where
  testEquality SInteger SInteger = Just Refl
  testEquality SBoolean SBoolean = Just Refl
  testEquality SByteStr SByteStr = Just Refl
  testEquality SStruct  SStruct  = Just Refl
  testEquality SContract SContract = Just Refl
  testEquality (SSArray a) (SSArray b) = (\Refl -> Just Refl) =<< testEquality a b
  testEquality _ _ = Nothing

type Id = String

data IntSign = Signed | Unsigned
  deriving (Eq, Show)

data TValueType (a :: ActType) where
  TInteger  :: Int -> IntSign -> TValueType AInteger
  TAddress  :: TValueType AInteger
  TBoolean  :: TValueType ABoolean
  TByteStr  :: TValueType AByteStr
  TStruct   :: [ValueType] -> TValueType AStruct
  TArray    :: SingI a => Int -> TValueType a -> TValueType (AArray a)
  TContract :: Id -> TValueType AContract
deriving instance Eq (TValueType a)
deriving instance Show (TValueType a)

instance TestEquality TValueType where
  testEquality (TInteger b1 s1) (TInteger b2 s2) | b1 == b2 && s1 == s2 = Just Refl
  testEquality TBoolean TBoolean = Just Refl
  testEquality TByteStr TByteStr = Just Refl
  testEquality TAddress TAddress = Just Refl
  testEquality (TContract c1) (TContract c2) | c1 == c2 = Just Refl
  testEquality (TArray n1 t1) (TArray n2 t2) | n1 == n2 = (\Refl -> Just Refl) =<< testEquality t1 t2
  testEquality (TStruct fs1) (TStruct fs2) | and (zipWith (==) fs1 fs2) = Just Refl
  testEquality _ _ = Nothing

data ValueType = forall (a :: ActType). SingI a => ValueType (TValueType a)
deriving instance Show ValueType

instance Eq (ValueType) where
  ValueType vt1 == ValueType vt2 = eqS'' vt1 vt2

-- | Compare equality of two things parametrized by types which have singletons.
eqS :: forall (a :: ActType) (b :: ActType) f t. (SingI a, SingI b, Eq (f a t)) => f a t -> f b t -> Bool
eqS fa fb = maybe False (\Refl -> fa == fb) $ testEquality (sing @a) (sing @b)

-- | The same but when the higher-kinded type has two type arguments
eqS' :: forall (a :: ActType) (b :: ActType) f t t'. (SingI a, SingI b, Eq (f a t t')) => f a t t' -> f b t t' -> Bool
eqS' fa fb = maybe False (\Refl -> fa == fb) $ testEquality (sing @a) (sing @b)

-- | The same but when the higher-kinded type has no type arguments
eqS'' :: forall (a :: ActType) (b :: ActType) f. (SingI a, SingI b, Eq (f a)) => f a -> f b -> Bool
eqS'' fa fb = maybe False (\Refl -> fa == fb) $ testEquality (sing @a) (sing @b)

-- Defines which singleton to retrieve when we only have the type, not the
-- actual singleton.
instance SingI 'AInteger where sing = SInteger
instance SingI 'ABoolean where sing = SBoolean
instance SingI 'AByteStr where sing = SByteStr
instance SingI 'AStruct  where sing = SStruct
instance SingI 'AContract  where sing = SContract
instance SingI a => SingI ('AArray a) where sing = SSArray (sing @a)

type family ActSingI (a :: ActType) :: Constraint where
  ActSingI (a :: ActType) = SingI a

-- | Extracts the base type from an array ActType or returns the type itself
-- for non-array types. Used when expanding an array expression into
-- expressions of its elements.
type family Base (a :: ActType) :: ActType where
  Base (AArray a) = Base a
  Base AInteger = AInteger
  Base ABoolean = ABoolean
  Base AByteStr = AByteStr
  Base AStruct  = AStruct
  Base AContract = AContract

flattenSType :: SType a -> SType (Base a)
flattenSType (SSArray s') = flattenSType s'
flattenSType SInteger  = SInteger
flattenSType SBoolean  = SBoolean
flattenSType SByteStr  = SByteStr
flattenSType SStruct   = SStruct
flattenSType SContract = SContract

-- | Reflection of an Act type into a haskell type. Used to define the result
-- type of the evaluation function.
type family TypeOf a where
  TypeOf 'AInteger = Integer
  TypeOf 'ABoolean = Bool
  TypeOf 'AByteStr = ByteString
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
fromAbiType (AbiTupleType _)    = AStruct
fromAbiType _ = error "Syntax.Types.actType: TODO"

fromAbiType' :: AbiType -> ValueType
fromAbiType' (AbiUIntType n)     = ValueType $ TInteger n Unsigned
fromAbiType' (AbiIntType  n)     = ValueType $ TInteger n Signed
fromAbiType' AbiAddressType      = ValueType TAddress
fromAbiType' AbiBoolType         = ValueType TBoolean
fromAbiType' (AbiBytesType n)    = if n <= 32 then ValueType (TInteger (n*8) Unsigned) else ValueType TByteStr
fromAbiType' AbiBytesDynamicType = ValueType TByteStr
fromAbiType' AbiStringType       = ValueType TByteStr
fromAbiType' (AbiArrayType n a)  = case fromAbiType' a of
  ValueType vt' -> ValueType $ TArray n vt'
fromAbiType' (AbiTupleType f)    = ValueType $ TStruct (fromAbiType' <$> V.toList f)
fromAbiType' _ = error "Syntax.Types.valueType: TODO"

toAbiType :: TValueType a -> AbiType
toAbiType (TInteger n Unsigned) = AbiUIntType n
toAbiType (TInteger n Signed)   = AbiIntType n
toAbiType TAddress              = AbiAddressType
toAbiType TBoolean              = AbiBoolType
toAbiType TByteStr              = AbiBytesDynamicType
toAbiType (TContract _)         = AbiAddressType
toAbiType (TStruct fs)          = AbiTupleType (V.fromList $ toAbiType' <$> fs)
  where toAbiType' (ValueType t) = toAbiType t
toAbiType (TArray n t)          = AbiArrayType n (toAbiType t) 

--valueToAbiType :: ValueType -> AbiType
--valueToAbiType (ValueType t) = toAbiType t

flattenValueType :: TValueType a -> (TValueType (Base a), Maybe (NonEmpty Int))
flattenValueType (TArray n a) = case flattenValueType a of
  (a', Nothing) -> (a', Just $ NonEmpty.singleton n)
  (a', l) -> (a', ((<|) n) <$> l)
flattenValueType (TInteger n s) = (TInteger n s, Nothing)
flattenValueType TAddress = (TAddress, Nothing)
flattenValueType TBoolean = (TBoolean, Nothing)
flattenValueType TByteStr = (TByteStr, Nothing)
flattenValueType (TStruct fs) = (TStruct fs, Nothing)
flattenValueType (TContract cid) = (TContract cid, Nothing)

toSType :: forall (a :: ActType). TValueType a -> SType a
--toSType _ = sing @a
toSType (TInteger _ _) = SInteger
toSType TBoolean = SBoolean
toSType TByteStr = SByteStr
toSType TAddress = SInteger
toSType (TStruct _) = SStruct
toSType (TContract _) = SContract
toSType (TArray _ t) = SSArray (toSType t)


someType :: ActType -> SomeType
someType AInteger = SomeType SInteger
someType ABoolean = SomeType SBoolean
someType AByteStr = SomeType SByteStr
someType AStruct = SomeType SStruct
someType AContract = SomeType SContract
someType (AArray a) = case someType a of
  (FromSome styp ) -> SomeType $ SSArray styp

--actType :: SType s -> ActType
--actType SInteger = AInteger
--actType SBoolean = ABoolean
--actType SByteStr = AByteStr
--actType (SSArray a) = AArray $ actType a
--
data SomeType where
  SomeType :: SingI a => SType a -> SomeType

-- | Pattern match on an 'SomeType' is if it were an 'SType'.
pattern FromSome :: () => (SingI a) => SType a -> SomeType
pattern FromSome t <- SomeType t
{-# COMPLETE FromSome #-}

---- | Pattern match on an 'AbiType' is if it were an 'SType'.
--pattern FromAbi :: () => (SingI a) => SType a -> AbiType
--pattern FromAbi t <- (someType . fromAbiType -> FromSome t)
--{-# COMPLETE FromAbi #-}
--
---- | Pattern match on an 'ActType' is if it were an 'SType'.
--pattern FromAct ::() => (SingI a) => SType a -> ActType
--pattern FromAct t <- (someType -> FromSome t)
--{-# COMPLETE FromAct #-}

-- | Pattern match on an 'ValueType' is if it were an 'SType'.
--pattern FromVType :: () => (SingI a) => SType a -> ValueType
--pattern FromVType t <- (someType . fromValueType -> FromSome t)
--{-# COMPLETE FromVType #-}

-- | Helper pattern to retrieve the 'SingI' instances of the type
-- represented by an 'SType'.
pattern SType :: () => (SingI a) => SType a
pattern SType <- Sing
{-# COMPLETE SType #-}

pattern VType :: () => (SingI a) => TValueType a
pattern VType <- (toSType -> SType)
{-# COMPLETE VType #-}
