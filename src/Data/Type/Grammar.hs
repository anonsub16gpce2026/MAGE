{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Type.Grammar where

import GHC.TypeLits
import Data.Type.Ord
import Data.Kind
import Data.Type.Attribution
import Data.Type.Rule
import Data.Type.Aspect
import Data.Type.Utils

type NT = Symbol
type ProdName = Symbol

data TNT = N NT | T Type

type GSym = TNT -- TODO: refactor

type data Prod = NT :=> [TNT]

-- | Grammar
type Grammar = [(ProdName, Prod)] -- ordered

type family AddProd (p :: (ProdName, Prod)) (g :: Grammar) :: Grammar where
  AddProd p g = Sort (p ': g) -- TODO: improve performance, insertion should be linear


-- | getter for grammar
type family GetProd (p :: ProdName) (g :: Grammar) :: Prod where
  GetProd pnam ( '(pnam, p) ': _ ) = p
  GetProd pnam ( '(_, p) ': ps ) = GetProd pnam ps
  GetProd pnam '[] = TypeError (Text "ERR: no prod in gram")

type family RHS (p :: Prod) :: [TNT] where
  RHS (_ :=> rhs) = rhs

type family l :+++ r where l :+++ r = AppendSymbol l r


type Schema = [(NT, AttributionTy, AttributionTy)]

type family S (nt :: NT) (s :: Schema):: AttributionTy where
  S nt '[] = TypeError (Text "nonter not in schema")
  S nt ( '(nt, _, syn) ': _) = syn
  S nt ( _ ': schema) = S nt schema
type family I (nt :: NT) (s :: Schema):: AttributionTy where
  I nt '[] = TypeError (Text "nonter not in schema")
  I nt ( '(nt, inh, _) ': _) = inh
  I nt ( _ ': schema) = I nt schema


type family TopRuleTyGram (g :: Grammar) (s :: Schema) :: AspectTy where
  TopRuleTyGram '[] _ = '[]
  TopRuleTyGram ( '(pnam, prod) ': g) s
     = '(pnam, TopR prod s) ': TopRuleTyGram g s
 
-- | "top" rule of a production for a given grammar/schema
type family TopRuleTyProd (g :: Grammar) (s :: Schema) (p :: ProdName)
   :: RuleTy where
  TopRuleTyProd g s p = TopR (GetProd p g) s

type family TopR (p :: Prod) (s :: Schema) :: RuleTy where
  TopR (lhs :=> rhs) s = (I lhs s ': TopRChiS rhs s)
                      :-> (S lhs s ': TopRChiI rhs s) 
type family TopRChiI (chi :: [TNT]) (s :: Schema) where
  TopRChiI '[] s = '[]
  TopRChiI ('N nt ': tnts) s = I nt s ': TopRChiI tnts s
  TopRChiI ('T t ': tnts) s = '[] ': TopRChiI tnts s
type family TopRChiS (chi :: [TNT]) (s :: Schema) where
  TopRChiS '[] s = '[]
  TopRChiS ('N nt ': tnts) s = S nt s ': TopRChiS tnts s
  TopRChiS ('T t ': tnts) s = '[ '("term", t)] ': TopRChiS tnts s


type instance ('[] :: Grammar) :< g = ()
type instance ( '(pnam, p) ': prds :: Grammar) :< ( '(pnam', p') : prds')
  = SubGramAux (Compare pnam pnam') ( '(pnam, p) ': prds :: Grammar) ( '(pnam', p') : prds')
type family SubGramAux (o :: Ordering) (g :: Grammar) (g' :: Grammar) where
  SubGramAux EQ ( '(pnam, p) ': prds :: Grammar) ( '(pnam', p) : prds')
    = prds :< prds'
  SubGramAux GT ( '(pnam, p) ': prds :: Grammar) ( '(pnam', p) : prds')
    = prds :< ( '(pnam', p) : prds')
  SubGramAux LT ( '(pnam, p) ': prds :: Grammar) ( '(pnam', p) : prds')
    = TypeError (Text "ERR: not a subgram")
