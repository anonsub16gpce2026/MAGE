{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.EADT where

import Data.Type.Grammar
import GHC.TypeLits
import Data.Type.Ord
import Data.Kind
import Data.Type.Utils
import Data.Proxy

data ArgList (g :: Grammar) (l :: [TNT]) where
  ArgNil  :: ArgList g '[]
  ArgCons :: EADT g t -> ArgList g ts -> ArgList g (t ': ts)

infixr 5 <<
(<<) = ArgCons

data EADT (g :: Grammar) (sym :: TNT) where
  Inner :: forall g nt p . (KnownSymbol p, KnownSymbol nt)
    => SSymbol p -> ArgList g (Args g nt p)
        -> EADT g ('N nt)
  Leaf  :: t -> EADT g ('T t)

class g :< g' =>
  Cast (g :: Grammar) (g' :: Grammar) where
  cast :: Proxy g -> Proxy g' -> EADT g tnt -> EADT g' tnt

-- type family CastChi (g :: Grammar) (g' :: Grammar) (chi :: [GSym]) where
--   CastChi g g' '[] = '[]
--   CastChi g g' ('T t ': chis) = 'T t ': CastChi g g' chis
--   CastChi g g' ('T t ': chis) = 'NT nt ': CastChi g g' chis

--instance g :< g' => Cast g g' where
--  cast pg pg' (Inner p args) = Inner p args

  
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

