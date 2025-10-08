module Data.Type.Attribute where

import GHC.TypeLits (Symbol)
import Data.Kind (Type)


type AttTy = (Symbol, Type)
