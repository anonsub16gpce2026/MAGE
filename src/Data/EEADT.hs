{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.EEADT where

import Data.Type.Grammar
import GHC.TypeLits
import Data.Type.Ord
import Data.Kind
import Data.Type.Utils
import Data.Proxy
import Data.EADT qualified as EADT

data EADT (g :: Grammar) (sym :: TNT) (p :: ProdName) where
  Inner :: forall g nt p . (KnownSymbol p, KnownSymbol nt)
    => SSymbol p -> ArgList g (EADT.Args g nt p)
        -> EADT g ('N nt) p
  Leaf  :: t -> EADT g ('T t) p

data ArgList (g :: Grammar) (l :: [TNT]) where
  ArgNil  :: ArgList g '[]
  ArgCons :: EADT g t p -> ArgList g ts -> ArgList g (t ': ts)

infixr 5 <<
(<<) = ArgCons

type family Args (g :: Grammar) (nt :: NT) (p :: ProdName) = (r :: [TNT]) where
  Args g nt p = -- Symbols2Types g nt
                (ArgsAux g g nt p)
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
   
