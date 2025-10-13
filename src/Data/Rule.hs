module Data.Rule where

import Data.Type.Rule
import Data.Attribution
import Data.Type.Utils
import Data.Attribute
import GHC.TypeLits hiding (SNat)
import Data.Type.Equality
import Unsafe.Coerce

infixr 5 :-
data Family (t :: FamilyTy) where
  Empty :: Family '[]
  (:-)  :: Attribution atts -> Family attrs -> Family (atts ': attrs)

-- | getter, by index
(.$) :: Family a -> SNat n -> Attribution (AtN n a)
(atts :- _)     .$ SZ     = atts
(_    :- attrs) .$ (SS n) = attrs .$ n
_ .$ _ = error "impossible"


-- | Projection/Cast
as :: Family l -> Family r -> Family (l `As` r)
as Empty Empty = Empty
as (att :- atts) (att' :- atts')
  = shrinkTo att att' :- atts `as` atts'
as _ _ = error "impossible"

-- | Theorem:
-- lemma :: Ext a b `As` a :~: a
-- lemma = undefined


-- | merging of families
(.+) :: Family t -> Family u -> Family (Ext t u)
Empty .+ Empty = Empty
(attr :- attrs) .+ (attr' :- attrs') = (attr .:+: attr') :- attrs .+ attrs'
_ .+ _ = error "impossible"


data Rule (r :: RuleTy) where
  MkRule :: {runRule :: Family inp -> Family out} -> Rule (inp :-> out)


type RuleEval = '[ '[], '[ '("eval", Int)], '[ '("eval", Int)]]
              :-> '[ '[ '("eval", Int)], '[], '[]]
rul_eval_add :: Rule RuleEval
rul_eval_add = MkRule $ \inp ->
  (MkAtt @"eval" ((inp .$ (SS SZ)) # SSymbol @"eval" + (inp .$ (SS $SS SZ)) # SSymbol @"eval")
   :. EmptyAtt)
   :- EmptyAtt :- EmptyAtt :- Empty

rul_size_add :: Rule (   '[ '[], '[ '("size", Int)], '[ '("size", Int)]]
                    :-> '[ '[ '("size", Int)], '[], '[]])
rul_size_add = MkRule $ \inp ->
  (MkAtt @"size" ((inp .$ (SS SZ)) # SSymbol @"size") :. EmptyAtt)
   :- EmptyAtt :- EmptyAtt :- Empty



(.+.) :: Rule (inp :-> out) -> Rule (inp' :-> out')
      -> Rule (Ext inp inp' :-> Ext out out')
(MkRule f) .+. (MkRule g)
  = MkRule $ \inp ->
  let out1 = f (Unsafe.Coerce.unsafeCoerce inp :: Family inp)
      out2 = g (Unsafe.Coerce.unsafeCoerce inp :: Family inp')
  in out1 .+ out2
