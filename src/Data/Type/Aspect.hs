{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Type.Aspect where

import Data.Type.Rule
import GHC.TypeLits
import Data.Type.Utils

type AspectTy = [(Symbol, RuleTy)]
type instance Sub (t :: RuleTy) u = t :< u

type family (asp :: AspectTy) :*: (asp' :: AspectTy) :: AspectTy where
  '[] :*: asp' = asp'
  asp :*: '[]  = asp
  ('(prd, r) ': asp) :*: ('(prd', r') ': asp')
    = CombineAsp (CmpSymbol prd prd') prd prd' r r' asp asp'
type family CombineAsp (o :: Ordering) (prd :: Symbol) (prd' :: Symbol)
                       (r :: RuleTy)(r' :: RuleTy)
                       (asp :: AspectTy) (asp' :: AspectTy) :: AspectTy where
  CombineAsp EQ prd _ r r' asp asp'
    = '(prd, r `Ext` r') ': asp :*: asp'
  CombineAsp LT prd prd' r r' asp asp'
    = '(prd, r) ': (asp :*: ( '(prd', r') ': asp'))
  CombineAsp GT prd prd' r r' asp asp'
    = '(prd', r') ': (('(prd, r) ': asp) :*: asp')

type family (a :: AspectTy) :# (l :: Symbol) :: RuleTy where
  ( '(l, r) ': asp) :# l = r
  ( '(l, r) ': asp) :# l' = asp :# l'


-- subtyping for aspects
type instance (l :: AspectTy) :< (m :: AspectTy) = SubType l m
