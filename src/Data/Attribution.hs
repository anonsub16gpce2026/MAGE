module Data.Attribution where

import Data.Type.Attribution
import Data.Attribute
import GHC.TypeLits
import Data.Type.Utils

infixr 5 :.
data Attribution (t :: AttributionTy) where
  EmptyAtt :: Attribution '[]
  (:.) :: KnownSymbol l
       => Att '(l,v) -> Attribution ts
       -> Attribution ('(l,v) ': ts)

-- | smart cons, keeping the attribution ordered
infixr 5 .+:
(.+:) :: KnownSymbol l
      => Att '(l,v) -> Attribution ts
      -> Attribution ('[ '(l,v)] :++ ts)
att  .+: EmptyAtt       = att :. EmptyAtt
att .+: r@(att' :. xs) =
  case cmpSymbol (getP att) (getP att') of
    LTI -> att :. r
    GTI -> att' :. (att .+: xs)
    EQI -> error "impossible" -- (type error)

-- | getter
infixr 8 #
(#) :: KnownSymbol l
    => Attribution ts -> SSymbol l -> Lookup l ts
(att :. atts) # l
  = case cmpSymbol l (getP att) of
      EQI -> getV att
      GTI -> atts # l
      LTI -> error "impossible"
EmptyAtt # _ = error "impossible"


-- | Merging attributions
infixr 5 .:+:
(.:+:) :: Attribution a -> Attribution b -> Attribution (a :++ b)
EmptyAtt       .:+: b        = b
a              .:+: EmptyAtt = a
l@(lv :. atts) .:+: r@(lv' :. atts')
  = case cmpSymbol (getP lv) (getP lv') of
      LTI -> lv :. (atts .:+: r)
      EQI -> error "impossible"
      GTI -> lv' :. (l .:+: atts')
  
-- | an example
example :: Attribution ['("1", Bool), '("2", ()), '("4", String)]
example
  = MkAtt @"1" True :. MkAtt @"2" () :. MkAtt @"4" "" :. EmptyAtt

t :: ()
t = example # SSymbol @"2"

castAttr :: (b :< a) => Attribution a -> Attribution b -> Attribution (a `As` b)
castAttr = castAttrAux
  where
    castAttrAux :: Attribution a -> Attribution b
                -> Attribution (a `As` b)
    castAttrAux _ EmptyAtt = EmptyAtt
    castAttrAux l@(att :. atts) r@(att' :. atts')
      = case cmpSymbol (getP att) (getP att') of
          EQI -> att :. (castAttrAux atts atts')
          LTI -> castAttrAux atts r
