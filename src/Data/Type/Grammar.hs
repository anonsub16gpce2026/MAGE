{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Type.Grammar where

import GHC.TypeLits
import Data.Type.Ord
import Data.Kind
  
type NT = Symbol
type ProdName = Symbol

data TNT = N NT | T Type

type data Prod = NT :=> [TNT]
type Grammar = [(ProdName, Prod)]

type family l :+++ r where l :+++ r = AppendSymbol l r

