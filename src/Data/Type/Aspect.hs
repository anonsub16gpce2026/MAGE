{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Type.Aspect where

import Data.Type.Rule
import GHC.TypeLits

type AspectTy = [(Symbol, RuleTy)]

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
