{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE PartialTypeSignatures #-}

module Chomsky.MiniAspectAG where

import Data.Type.Attribution
import Data.Attribution
import Data.Type.Rule
import Data.Rule
import Data.Attribute
import Data.Type.Utils
import Data.Type.Aspect
import Data.Aspect
import Data.Type.Grammar
import qualified Data.EADT
import Data.Chomsky.EADT
import Data.Grammar

import Data.Proxy

--import MiniAspectAG hiding (sem)
import MiniAspectAG qualified as M
import MiniAspectAG (SemFuncTy, SemFunc(..), SCh, ICh, (:==>))
import Data.Chomsky.EADT qualified as C

import Unsafe.Coerce

import Data.Kind
import GHC.TypeLits
import Data.Type.Equality


sem :: (KnownSymbol p) =>
          Proxy g -> Proxy (a :: Schema) -> Aspect (TopRuleTyGram g a)
       -> EADT g sym p
       -> Attribution (II sym a) -> Attribution (SS sym a)
sem g a r (Leaf v) = \inp -> (singAttr v)
sem g a r t = semA g a r t

kn :: (SemFunc (i :==> o), SemFunc (i' :==> o') ) -> Family '[i, i']
   -> Family '[o,o']
kn (SemFunc f, SemFunc g) (c1 :- c2 :- _) = f c1 :- g c2 :- EmptyFam

knit :: Rule (ip ': o ': o' ': '[] :-> sp ': i ': i' ': '[])
     -> (SemFunc (i :==> o), SemFunc (i' :==> o') )
     -> Attribution ip
     -> Attribution sp
knit (MkRule rul) fc ip
  = let (sp :- ic) = rul (ip :- sc)
        sc         = kn fc ic
    in sp

type family BuildFC (g :: Grammar) (a :: Schema) (r :: AspectTy)
                    (p :: ProdName)(c1 :: GSym)(c2 :: GSym)
  :: Type
 where
  BuildFC g a r p c1 c2
     = (SemFunc (II c1 a :==> SS c1 a),
        SemFunc (II c2 a :==> SS c2 a))
  
type family Wrap1 (t :: SemFuncTy) = r | r -> t
type instance Wrap1 t = SemFunc t

type family WrapSFT (p :: (SemFuncTy, SemFuncTy)) where
  WrapSFT '(t,u) = (Wrap1 t, Wrap1 u)
  
-- type family WrapSFT (t :: (SemFuncTy, SemFuncTy))
--    :: r | r -> t where
--   WrapSFT '(t,u) = (SemFunc t, SemFunc u)

-- buildFC :: (KnownSymbol p, KnownSymbol p1, KnownSymbol p2) =>
--           Proxy g -> Proxy a -> Aspect r -> SSymbol p
--         -> Proxy chis -> EADT g s1 p1 -> EADT g s2 p2
--         -> (BuildFC g a r p s1 s2)
buildFC g a r p Proxy t1 t2
  = (SemFunc (sem g a r t1), SemFunc (sem g a r t2))
-- buildFC g a r p Proxy t1@(Leaf x) t2@(Leaf y)
--   = (SemFunc (semA g a r t1), SemFunc (semA g a r t2))


semA :: (KnownSymbol p, TopRuleTyGram g a ~ r) =>
          Proxy g -> Proxy (a :: Schema) -> Aspect r
       -> EADT g s p
       -> Attribution ip -> Attribution sp
semA g a r t@(Inner prd c1 c2) = semP prd g a r t
--semA g a r t@(Leaf{}) = sem g a r t

semP :: (TopRuleTyGram g a ~ r) => SSymbol p -> Proxy g -> Proxy (a :: Schema) -> Aspect r
     -> EADT g ('N nt) p 
     -> Attribution ip -> Attribution sp
semP p g a r (Inner prd c1 c2) =
    case sameSymbol p prd of
      Just Refl -> knit (unsafeCoerce (r ## p))
         $ buildFC g a r p Proxy c1 c2
