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
import Data.Grammar

import GHC.TypeLits
import Data.Kind
import Data.Type.Equality
import Data.Proxy
import Unsafe.Coerce

import Control.IMonad
import Control.Monad qualified as M
import Control.Monad.Reader

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

type family IP (io :: RuleTy) :: AttributionTy where
  IP (ip ': sc :-> _) = ip
type family SP (io :: RuleTy) :: AttributionTy where
  SP (_ :-> sp ': ic) = sp


kn :: HKList SemFunc (fcs :: [SemFuncTy]) -> Family (ICh fcs)
   -> Family (SCh fcs)
kn HKNil _ = EmptyFam
kn (HKCons fc fcs) (c :- cs)
  = case fc of
      SemFunc f -> f c :- kn fcs cs

knit :: Rule (ip ': SCh fcs :-> sp ': ICh fcs)
     -> HKList SemFunc fcs
     -> Attribution ip
     -> Attribution sp
knit (MkRule rul) fc ip
  = let (sp :- ic) = rul (ip :- sc)
        sc         = kn fc ic
    in sp

type family BuildFC (g :: Grammar) (a :: Schema) (r :: AspectTy)
                    (p :: ProdName)(chis :: [GSym]) :: [SemFuncTy] where
  BuildFC g a r p '[] = '[]
  BuildFC g a r p ('T t ': chis)
     = '[] :==> '[ '("term", t)] ': BuildFC g a r p chis
  BuildFC g a r p ('N nt ': chis)
     = I nt a :==> S nt a ': BuildFC g a r p chis

buildFC :: Proxy g -> Proxy a -> Aspect r -> SSymbol p
        -> Proxy chis -> ArgList g chis
        -> HKList SemFunc (BuildFC g a r p chis)
buildFC g a r p Proxy ArgNil = HKNil
buildFC g a r p Proxy (ArgCons (Leaf t) args)
  = HKCons (SemFunc $ \_ -> MkAtt t :. EmptyAtt) $ buildFC  g a r p Proxy args
buildFC g a r p Proxy (ArgCons t@(Inner prd vchis) args)
  = HKCons (SemFunc $ semA g a r t) $ buildFC  g a r p Proxy args


semA ::   Proxy g -> Proxy (a :: Schema) -> Aspect r
       -> EADT g ('N nt) 
       -> Attribution ip -> Attribution sp
semA g a r t@(Inner prd args) = semP prd g a r t

semP :: KnownSymbol p
     => SSymbol p -> Proxy g -> Proxy (a :: Schema) -> Aspect r -> EADT g ('N nt) 
     -> Attribution ip -> Attribution sp
semP p g a r (Inner prd args) =
    case sameSymbol p prd of
      Just Refl -> knit (unsafeCoerce (r ## p)) $ buildFC g a r p Proxy args

sem ::    Proxy g -> Proxy (a :: Schema) -> Aspect (TopRuleTyGram g a)
       -> EADT g ('N nt) 
       -> Attribution (I nt a) -> Attribution (S nt a)
sem = semA



-- Indexed Monad instances to build combinators
instance Return (Reader (Family f)) where
  preturn a = M.return a

instance Bind (Reader (Family f1)) (Reader (Family f2)) where
  type (Reader (Family f1)) :>>= (Reader (Family f2))
     = Reader (Family (Ext f1 f2))
  m >>=. f = reader $ \inp ->
    let i1 = unsafeCoerce inp
        i2 = unsafeCoerce inp
        out = runReader (f (runReader m i1)) i2
    in out  
