{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}

module Act.Traversals (TraversableTerm(..), mapExp) where

import Data.Functor.Identity
import Act.Syntax.Typed
import Prelude hiding (LT, GT)

-- | Generic operations over AST terms
class TraversableTerm a where
  mapTermM  :: Monad m => (forall b t . Exp b t -> m (Exp b t)) -> a -> m a

  mapTerm :: (forall b t . Exp b t -> Exp b t) -> a -> a
  mapTerm f e = runIdentity (mapTermM (Identity . f) e)

instance TraversableTerm (Exp a t) where
  mapTermM = mapExpM

instance TraversableTerm (TypedExp t) where
  mapTermM = mapTypedExpM

instance TraversableTerm (Ref k t) where
  mapTermM = mapRefM

mapExpM :: Monad m => (forall a . Exp a t -> m (Exp a t)) -> Exp b t -> m (Exp b t)
mapExpM f = \case
  --booleans
  And p a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (And p a' b')
  Or p a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (Or p a' b')
  Impl p a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (Impl p a' b')
  Neg p a -> do
    a' <- mapExpM f a
    f (Neg p a')
  LT p a ta b tb -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (LT p a' ta b' tb)
  LEQ p a ta b tb -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (LEQ p a' ta b' tb)
  GEQ p a ta b tb -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (GEQ p a' ta b' tb)
  GT p a ta b tb -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (GT p a' ta b' tb)
  LitBool p a -> f (LitBool p a)

  --integers

  Add p a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (Add p a' b')
  Sub p a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (Sub p a' b')
  Mul p a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (Mul p a' b')
  Div p a ta b tb -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (Div p a' ta b' tb)
  Mod p a ta b tb -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (Mod p a' ta b' tb)
  Exp p a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (Exp p a' b')
  LitInt p a -> f (LitInt p a)
  IntEnv p a -> f (IntEnv p a)

  --bounds
  IntMin p a -> f (IntMin p a)
  IntMax p a -> f (IntMax p a)
  UIntMin p a -> f (UIntMin p a)
  UIntMax p a -> f (UIntMax p a)
  InRange p a b -> do
    b' <- mapExpM f b
    f (InRange p a b')

  --bytestrings

  Cat p a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (Cat p a' b')
  Slice p a b c -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    c' <- mapExpM f c
    f (Slice p a' b' c')
  ByStr p a -> f (ByStr p a)
  ByLit p a -> f (ByLit p a)
  ByEnv p a -> f (ByEnv p a)

  Array p l -> do
    l' <- mapM f l
    f (Array p l')

  --contracts

  Create p n as v -> do
    as' <- mapM (mapTypedExpM f) as
    v' <- mapM (mapExpM f) v
    f (Create p n as' v')

  --polymorphic

  Eq p s a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (Eq p s a' b')
  NEq p s a b -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    f (NEq p s a' b')

  ITE p a b c -> do
    a' <- mapExpM f a
    b' <- mapExpM f b
    c' <- mapExpM f c
    f (ITE p a' b' c')
  VarRef p t r -> do
    r' <- mapRefM f r
    f (VarRef p t r')
  Address p c x -> do
    x' <- mapExpM f x
    f (Address p c x')
  Mapping p kt vt kvs -> do
    kvs' <- mapM (\(k, v) -> do
      k' <- mapExpM f k
      v' <- mapExpM f v
      pure (k', v')) kvs
    f (Mapping p kt vt kvs')
  MappingUpd p r kt vt kvs -> do
    r' <- mapRefM f r
    kvs' <- mapM (\(k, v) -> do
      k' <- mapExpM f k
      v' <- mapExpM f v
      pure (k', v')) kvs
    f (MappingUpd p r' kt vt kvs')

mapExp :: (forall a . Exp a t -> Exp a t) -> Exp b t -> Exp b t
mapExp f e = runIdentity (mapExpM (Identity . f) e)

mapTypedExpM :: Monad m => (forall a . Exp a t -> m (Exp a t)) -> TypedExp t -> m (TypedExp t)
mapTypedExpM f (TExp t e) = do
  e' <- f e
  pure $ TExp t e'

mapRefM :: Monad m => (forall a . Exp a t -> m (Exp a t)) -> Ref k t -> m (Ref k t)
mapRefM f = \case
  SVar p time c a -> pure (SVar p time c a)
  CVar p a b -> pure (CVar p a b)
  RArrIdx p a b n -> do
    a' <- mapRefM f a
    b' <- mapExpM f b
    pure $ RArrIdx p a' b' n
  RMapIdx p a b -> do
    a' <- mapTypedRefM f a
    b' <- mapTypedExpM f b
    pure $ RMapIdx p a' b'
  RField p r a b -> do
    r' <- mapRefM f r
    pure $ RField p r' a b


mapTypedRefM :: Monad m => (forall a . Exp a t -> m (Exp a t)) -> TypedRef t -> m (TypedRef t)
mapTypedRefM f (TRef t k r) = do
  r' <- mapRefM f r
  pure $ TRef t k r'
