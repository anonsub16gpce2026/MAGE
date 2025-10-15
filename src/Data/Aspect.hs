module Data.Aspect where

import Data.Type.Aspect ( type (:*:), AspectTy, type (:#) )
import Data.Type.Rule ( RuleTy(type (:->)) )
import Data.Rule ( (.+.), Rule )
import GHC.TypeLits
    ( KnownSymbol,
      SSymbol,
      cmpSymbol,
      decideSymbol,
      OrderingI(GTI, EQI, LTI),
      symbolSing)
import Data.Type.Equality
    ( type (:~:)(Refl) )
import Unsafe.Coerce (unsafeCoerce)

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

(##) :: KnownSymbol prd => Aspect asp -> SSymbol prd -> Rule (asp :# prd)
(ConsAspect prd rul asp) ## prd'
  = case decideSymbol prd prd' of
      Right Refl -> rul
      Left _  -> Unsafe.Coerce.unsafeCoerce (asp ## prd')
                                     

singAsp :: KnownSymbol prd => Rule (i :-> o) ->  Aspect '[ '(prd, i :-> o)]
singAsp rul = ConsAspect symbolSing rul EmptyAspect
