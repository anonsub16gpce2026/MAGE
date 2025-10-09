module Data.Rule where

import Data.Type.Rule
import Data.Attribution
import Data.Type.Utils
import Data.Attribute
import GHC.TypeLits hiding (SNat)

infixr 5 :-
data Family (t :: FamilyTy) where
  Empty :: Family '[]
  (:-)  :: Attribution atts -> Family attrs -> Family (atts ': attrs)

(.$) :: Family a -> SNat n -> Attribution (AtN n a)
(atts :- _)     .$ SZ     = atts
(_    :- attrs) .$ (SS n) = attrs .$ n
_ .$ _ = error "impossible"


-- | merging of families
(.+) :: Family t -> Family u -> Family (Ext t u)
Empty .+ Empty = Empty
(attr :- attrs) .+ (attr' :- attrs') = (attr .:+: attr') :- attrs .+ attrs'
_ .+ _ = error "impossible"


data Rule (r :: RuleTy) where
  MkRule :: {runRule :: Family inp -> Family out} -> Rule (inp :-> out)

exampleRule :: Rule (   '[ '[], '[ '("eval", Int)], '[ '("eval", Int)]]
                    :-> '[ '[ '("eval", Int)], '[], '[]])
exampleRule = MkRule $ \inp ->
  (MkAtt @"eval" ((inp .$ (SS SZ)) # SSymbol @"eval") :. EmptyAtt)
   :- EmptyAtt :- EmptyAtt :- Empty

-- (.+.) :: Rule (inp :-> out) -> Rule (inp' :-> out')
--       -> Rule (Ext inp inp' :-> Ext out out')
-- (MkRule f) .+. (MkRule g)
--   = MkRule $ \inp -> let out1 = f inp
--                          out2 = g inp
--                      in out1
