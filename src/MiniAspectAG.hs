{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module MiniAspectAG where

import Data.Type.Attribution
import Data.Attribution
import Data.Type.Rule
import Data.Rule
import Data.Attribute
import Data.Type.Utils
import Data.Type.Aspect
import Data.Aspect
import Data.Type.Grammar
import Data.EADT

import GHC.TypeLits
import Data.Kind
import Data.Type.Equality
import Data.Proxy
import Unsafe.Coerce

-- | stores semantic functions, i.e. functions from inherited attributes
-- (input) to synthesized attributes (output)
data SemFunc (f :: SemFuncTy) where
  SemFunc :: {runSemFunc :: Attribution i -> Attribution o}
          -> SemFunc (i :==> o)

-- | type data to store the type-level information of a Ssemantic Function
type data SemFuncTy =
  AttributionTy :==> AttributionTy


type family ICh (r :: [SemFuncTy]) :: [AttributionTy] where
  ICh '[] = '[]
  ICh (ic :==> sc ': fcs) = ic ': ICh fcs
type family SCh (r :: [SemFuncTy]) :: [AttributionTy] where
  SCh '[] = '[]
  SCh (ic :==> sc ': fcs) = sc ': SCh fcs

kn :: HKList SemFunc (fcs :: [SemFuncTy]) -> Family (ICh fcs)
   -> Family (SCh fcs)
kn HKNil _ = EmptyFam
kn (HKCons fc fcs) (c :- cs)
  = case fc of
      SemFunc f -> f c :- kn fcs cs


knit :: Rule ( ip ': SCh fcs :-> sp ': ICh fcs) -> HKList SemFunc fcs
     -> Attribution ip -> Attribution sp
knit (MkRule rul) fc ip
  = let (sp :- ic) = rul (ip :- sc)
        sc         = kn fc ic
    in sp



lemma_rul_get :: Proxy g -> Proxy a -> SSymbol prd ->
             TopRuleTyGram g a :# prd :~: TopRuleTyProd g a prd
lemma_rul_get g a p = unsafeCoerce Refl


-- class FC (g :: Grammar)  (a   :: Schema)
--          (r :: AspectTy) (p   :: ProdName) (nt :: NT)
--          (tnt :: [TNT]) where
-- --  type BuildFC g a r p nt :: [SemFuncTy]
--   buildFC' :: Proxy g -> Proxy a -> Aspect r -> Proxy p -> Proxy nt
--            -> Proxy tnt -> HList (Args g nt p)
--            -> HKList SemFunc (BuildFC g a r p nt tnt)

type family BuildFC (g :: Grammar)  (a   :: Schema)
                    (r :: AspectTy) (p   :: ProdName)
                    (nt :: NT) (args  :: [Type])
     :: [SemFuncTy]
  where
  BuildFC g a r p nt '[] = '[]
  BuildFC g a r p nt (SomeVariant g nt' ': ts)
    = I nt' a :==> S nt' a ': BuildFC g a r p nt ts
  BuildFC g a r p nt (t ': ts)
    = '[] :==> '[ '( "term", t)] ': BuildFC g a r p nt ts

buildFC :: Proxy g -> Proxy a -> Aspect r -> Proxy p -> Proxy nt
        -> HList (Args g nt p)
        -> HKList SemFunc (BuildFC g a r p nt (Args g nt p)) 
buildFC g a r p nt HNil = HKNil
buildFC g a r p nt (t ::: ts) = undefined
