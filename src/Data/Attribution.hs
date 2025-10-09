module Data.Attribution where

import Data.Type.Attribution
import Data.Attribute
import GHC.TypeLits

import Data.Type.Utils
--import Data.Proxy

infixr 5 :.
data Attribution (t :: AttributionTy) where
  EmptyAtt :: Attribution '[]
  (:.) :: KnownSymbol l
       => Att '(l,v) -> Attribution ts
       -> Attribution ('(l,v) ': ts)

infixr 5 .:
(.:) :: KnownSymbol l
      => Att '(l,v) -> Attribution ts
      -> Attribution ('[ '(l,v)] :++ ts)
att  .: EmptyAtt       = att :. EmptyAtt
att .: r@(att' :. xs) =
  case cmpSymbol (getP att) (getP att') of
    LTI -> att :. r
    GTI -> att' :. (att .: xs)
    EQI -> error "impossible" -- (type error)


infixr 8 #
(#) :: KnownSymbol l
    => Attribution ts -> SSymbol l -> Lookup l ts
(att :. atts) # l
  = case cmpSymbol l (getP att) of
      EQI -> getV att
      GTI -> atts # l
      LTI -> error "impossible"
EmptyAtt # _ = error "impossible"

example :: Attribution ['("1", Bool), '("2", ()), '("4", String)]
example
  = MkAtt @"1" True
  :. MkAtt @"2" ()
  :. MkAtt @"4" ""
  :. EmptyAtt

t :: ()
t = example # SSymbol @"2"
