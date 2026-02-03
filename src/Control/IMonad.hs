{-# LANGUAGE TypeFamilies #-}

module Control.IMonad where

import Data.Kind (Type)

class Return (m :: Type -> Type) where
  preturn :: a -> m a

class Bind (m :: Type -> Type) (m' :: Type -> Type) where
  type m :>>= m' :: Type -> Type
  (>>=.) :: m a -> (a -> m' b) -> (m :>>= m') b
  (>>.)  :: m a -> m' b -> (m :>>= m') b
  m >>. f = m >>=. \_ -> f

class (Return m) => App m where {}
