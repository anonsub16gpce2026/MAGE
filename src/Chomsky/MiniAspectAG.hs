{-# LANGUAGE TypeFamilies #-}
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
       -> EADT g ('N nt) p
       -> Attribution (I nt a) -> Attribution (S nt a)
sem = semA 

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
  :: (SemFuncTy, SemFuncTy)
 where
  BuildFC g a r p ('N nt1) ('N nt2)
     = '(I nt1 a :==> S nt1 a,  I nt2 a :==> S nt2 a)
type family WrapSFT (t :: (SemFuncTy, SemFuncTy)) :: Type where
  WrapSFT '(t,u) = (SemFunc t, SemFunc u)

buildFC :: (KnownSymbol p, KnownSymbol p1, KnownSymbol p2) =>
          Proxy g -> Proxy a -> Aspect r -> SSymbol p
        -> Proxy chis -> EADT g ('N nt1) p1 -> EADT g ('N nt2) p2
        -> WrapSFT (BuildFC g a r p ('N nt1) ('N nt2))
buildFC g a r p Proxy t1 t2
  = (SemFunc (semA g a r t1), SemFunc (semA g a r t2))


semA :: (KnownSymbol p) =>
          Proxy g -> Proxy (a :: Schema) -> Aspect r
       -> EADT g ('N nt) p
       -> Attribution ip -> Attribution sp
semA g a r t@(Inner prd c1 c2) = semP prd g a r t

semP :: KnownSymbol p
     => SSymbol p -> Proxy g -> Proxy (a :: Schema) -> Aspect r
     -> EADT g ('N nt) p 
     -> Attribution ip -> Attribution sp
semP p g a r (Inner prd c1 c2) =
    case sameSymbol p prd of
      Just Refl -> knit (unsafeCoerce (r ## p))
         $ buildFC g a r p Proxy c1 c2
