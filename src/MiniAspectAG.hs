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

semTop :: Proxy (g :: Grammar) -> Proxy (a :: Schema)
       -> Aspect (TopRuleTyGram g a) -> Variant g nt prd
       -> Attribution (I nt a) -> Attribution (S nt a)
semTop pg pa asp (Variant prd args)
  = undefined knit (asp ## prd) undefined

buildFC :: Proxy (g :: Grammar) -> Proxy (a :: Schema)
        -> Proxy nt -- ambg types
        -> Aspect (TopRuleTyGram g a)
        -> SSymbol prd
        -> HList (Args g nt prd)
        -> HKList SemFunc (BuildFC g a prd)
buildFC pg pa pnt asp prd HNil = _


type family BuildFC (g :: Grammar)(a :: Schema)(prd :: ProdName) :: [SemFuncTy]
  where
    BuildFC g a p = BuildFCProd (GetProd p g) a
type family BuildFCProd (g :: Prod)(a :: Schema) :: [SemFuncTy] where
  BuildFCProd (lhs :=> rhs) a = BuildFCTNT rhs a
type family BuildFCTNT (rhs :: [TNT])(a :: Schema) :: [SemFuncTy] where
  BuildFCTNT '[] a = '[]
  BuildFCTNT ('N s ': tnt) a = I s a :==> S s a ': BuildFCTNT tnt a
  BuildFCTNT ('T t ': tnt) a = ( '[] :==> '[ '("term", t)]) ': BuildFCTNT tnt a


lemma_rul_get :: Proxy g -> Proxy a -> SSymbol prd ->
             TopRuleTyGram g a :# prd :~: TopRuleTyProd g a prd
lemma_rul_get g a p = unsafeCoerce Refl
