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
  EmptyFam :: Family '[]
  (:-)  :: Attribution atts -> Family attrs -> Family (atts ': attrs)

-- | getter, by index
(.$) :: Family a -> SNat n -> Attribution (AtN n a)
(atts :- _)     .$ SZ     = atts
(_    :- attrs) .$ (SS n) = attrs .$ n
_ .$ _ = error "impossible"


-- | Projection/CcastFamt
castFam :: (r :< l) =>
    Family l -> Family r -> Family (l `As` r)
castFam EmptyFam EmptyFam = EmptyFam
castFam (att :- atts) (att' :- atts')
  = castAttr att att' :- atts `castFam` atts'
castFam _ _ = error "impossible"

-- | Theorem:
-- lemma :: Ext a b `CastFam` a :~: a
-- lemma = undefined


-- | merging of families
(.+) :: Family t -> Family u -> Family (Ext t u)
EmptyFam .+ EmptyFam = EmptyFam
(attr :- attrs) .+ (attr' :- attrs')
  = (attr .:+: attr') :- attrs .+ attrs'
_ .+ _ = error "impossible"


data Rule (r :: RuleTy) where
  MkRule :: {runRule :: Family inp -> Family out} -> Rule (inp :-> out)


(.+.) :: Rule (inp :-> out) -> Rule (inp' :-> out')
      -> Rule (Ext inp inp' :-> Ext out out')
(MkRule f) .+. (MkRule g)
  = MkRule $ \inp ->
  let out1 = f (Unsafe.Coerce.unsafeCoerce inp :: Family inp)
      out2 = g (Unsafe.Coerce.unsafeCoerce inp :: Family inp')
  in out1 .+ out2

