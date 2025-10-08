module Data.Attribution where

import Data.Type.Attribution
import Data.Attribute
import GHC.TypeLits

data Attribution (t :: AttributionTy) where
  EmptyAtt :: Attribution '[]
  (:.) :: KnownSymbol l
       => Att '(l,v) -> Attribution ts
       -> Attribution ('(l,v) ': ts)

(.:) :: KnownSymbol l
      => Att '(l,v) -> Attribution ts
      -> Attribution ('[ '(l,v)] :++ ts)
t   .: EmptyAtt       = t :. EmptyAtt
att .: r@(att' :. xs) =
  case cmpSymbol (getP att) (getP att') of
    LTI -> att :. r
    GTI -> att' :. (att .: xs)
    EQI -> error "impossible" -- (type error)
