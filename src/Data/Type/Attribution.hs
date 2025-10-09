{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Type.Attribution where

import Data.Type.Attribute
import Data.Type.Utils

type AttributionTy = [AttTy]

type family (l :: AttributionTy) :++ (r :: AttributionTy)
  :: AttributionTy where
  l :++ r = Merge l r
  -- todo: Type errors

-- | beware, it is orphan
type instance (l :: AttributionTy) :< (r :: AttributionTy)
  = SubType l r
