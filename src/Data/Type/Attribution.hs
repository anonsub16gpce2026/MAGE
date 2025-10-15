{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Type.Attribution where

import Data.Type.Attribute
import Data.Type.Utils
import GHC.TypeLits
import Data.Kind
import Data.Type.Ord

type AttributionTy = [AttTy]

type family (l :: AttributionTy) :++ (r :: AttributionTy)
  :: AttributionTy where
  l :++ r = Merge l r
  -- todo: Type errors

-- | beware, it is orphan
type instance (l :: AttributionTy) :< (r :: AttributionTy)
  = SubType l r


type instance  As (xs :: AttributionTy) '[] = '[]
type instance  As ( '(l,  v)  ': xs :: AttributionTy)
                  ( '(l', v') ': ys :: AttributionTy)
  =  AsAuxAttribution (Compare l l') '(l, v) '(l', v') xs ys
type family AsAuxAttribution (o :: Ordering)
   (lv :: (Symbol, Type)) (lv' :: (Symbol, Type))
   (xs :: AttributionTy) (ys :: AttributionTy) where
  AsAuxAttribution EQ '(l, v) '(l, v') xs ys = '(l,v) ': As xs ys
  AsAuxAttribution LT '(l, v) '(l1, v1) xs ys = As xs ( '(l1, v1) ': ys)
