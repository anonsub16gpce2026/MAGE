module Data.Aspect where

import Data.Type.Aspect
import Data.Type.Rule
import Data.Rule
import GHC.TypeLits

data Aspect (t :: AspectTy) where
  EmptyAspect :: Aspect '[]
  ConsAspect  :: KnownSymbol prd => SSymbol prd -> Rule (i :-> o) -> Aspect t
              -> Aspect ( '(prd, i :-> o) ': t)

(.:*:) :: Aspect asp -> Aspect asp' -> Aspect (asp :*: asp')
EmptyAspect .:*: asp = asp
asp .:*: EmptyAspect = asp
l@(ConsAspect prd rul asp) .:*: r@(ConsAspect prd' rul' asp')
  = case cmpSymbol prd prd' of
      EQI -> ConsAspect prd (rul .+. rul') $ asp .:*: asp'
      LTI -> ConsAspect prd rul $ asp .:*: r
      GTI -> ConsAspect prd' rul' $ l .:*: asp'

singAsp :: KnownSymbol prd => Rule (i :-> o) ->  Aspect '[ '(prd, i :-> o)]
singAsp rul = ConsAspect SSymbol rul EmptyAspect
