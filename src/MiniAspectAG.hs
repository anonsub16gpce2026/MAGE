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


-- | stores semantic functions, i.e. functions from inherited attributes
-- (input) to synthesized attributes (output)
data SemFunc (f :: SemFuncTy) where
  SemFunc :: {runSemFunc :: Attribution i -> Attribution o}
          -> SemFunc (i :==> o)

-- | type data to store the type-level information of a Ssemantic Function
type data SemFuncTy =
  AttributionTy :==> AttributionTy


-- class Kn (fcs :: [SemFuncTy]) where 
--   kn :: HKList SemFunc (fcs :: [SemFuncTy]) -> Family (ICh fcs)
--      -> Family (SCh fcs)
-- instance Kn '[] where
--   kn _ _ = EmptyFam
-- instance Kn fcs => Kn (ic :==> sc ': fcs) where
--   kn (HKCons fc fcs) (c :- cs) = runSemFunc fc c :- kn fcs cs

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

knit :: () --(ICh fcs ~ ic, SCh fcs ~ sc)
     => Rule ( ip ': SCh fcs :-> sp ': ICh fcs) -> HKList SemFunc fcs
     -> Attribution ip -> Attribution sp
knit (MkRule rul) fc ip
  = let (sp :- ic) = rul (ip :- sc)
        sc         = kn fc ic
    in sp

-- type family BuildFC (asp :: AspectTy) (args :: [Type]) (g :: Grammar)
--                     (nt :: NT) (p :: ProdName) :: [SemFuncTy]
--  where
--   BuildFC asp '[] g nt p = '[]
--   BuildFC asp (EADT g nt' ': args) g nt p = 

-- buildFC :: Aspect asp -> HList (Args g nt p)
--         -> HKList SemFunc (BuildFC asp (Args g nt p) g nt p)
