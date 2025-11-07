{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.EADT where

import Data.Type.Grammar
import GHC.TypeLits
import Data.Type.Ord
import Data.Kind
import Data.Type.Utils

data ArgList (g :: Grammar) (l :: [TNT]) where
  ArgNil  :: ArgList g '[]
  ArgCons :: EADT g t -> ArgList g ts -> ArgList g (t ': ts)

infixr 5 <<
(<<) = ArgCons

data EADT (g :: Grammar) (sym :: TNT) where
  Inner :: forall g nt p . (KnownSymbol p, KnownSymbol nt) => SSymbol p -> ArgList g (Args g nt p)
        -> EADT g ('N nt)
  Leaf  :: t -> EADT g ('T t)

-- type family Symbols2Types (g :: Grammar) (nt :: NT)
--                           (s :: [TNT]) :: [Type] where
--   Symbols2Types g nt '[] = '[]
--   Symbols2Types g nt ( 'T t ': tnts) = EADT g ('T t) ': Symbols2Types g nt tnts
--   Symbols2Types g nt ( 'N n ': tnts)
--     = EADT g ('N nt) ': Symbols2Types g nt tnts

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
   
