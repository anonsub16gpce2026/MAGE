{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.EADT where

import Data.Type.Grammar
import GHC.TypeLits
import Data.Type.Ord
import Data.Kind

data HList (t :: [Type]) where
  HNil :: HList '[]
  (:::) :: t -> HList l -> HList (t ': l)
infixr 5 :::

data SomeVariant (g :: Grammar) (nt :: NT) where
  SV :: Variant g nt p -> SomeVariant g nt

data Variant (g :: Grammar) (nt :: NT) (p :: ProdName) where
  Variant :: HList (Args g nt p) -> Variant g nt p


type family Symbols2Types (g :: Grammar) (nt :: NT)
                          (p :: ProdName) (s :: [TNT]) :: [Type] where
  Symbols2Types g nt p '[] = '[]
  Symbols2Types g nt p ( T t ': tnts) = t ': Symbols2Types g nt p tnts
  Symbols2Types g nt p ( N n ': tnts) = SomeVariant g nt ': Symbols2Types g nt p tnts

type family Args (g :: Grammar) (nt :: NT) (p :: ProdName) :: [Type] where
  Args g nt p = Symbols2Types g nt p (ArgsAux g g nt p)
type family ArgsAux (h :: Grammar) (g :: Grammar) (nt :: NT) (p :: ProdName)
   :: [TNT]
 where
  ArgsAux h '[] nt pnam
    = TypeError (Text ( "production: " :+++ pnam :+++ "of nonterminal:" :+++ nt
                    :+++ "do not belong to grammar:") :$$:  ShowType h)
  ArgsAux h ('(prdnam, lhs :=> rhs) ': prds) nt pnam
    = ArgsAux' h (Compare prdnam pnam) (lhs :=> rhs) prds nt pnam
type family ArgsAux' (h :: Grammar) (o :: Ordering)
                     (prod :: Prod) (g :: Grammar)
                     (nt :: NT) (p :: ProdName) :: [TNT]
 where
   ArgsAux' h EQ (lhs :=> rhs) g nt pnam = rhs
   ArgsAux' h LT (lhs :=> rhs) g nt pnam = ArgsAux h g nt pnam
   
