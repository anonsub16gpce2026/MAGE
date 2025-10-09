module Data.Attribute where

import Data.Type.Attribute

import Data.Proxy
import GHC.TypeLits


pAtt :: Proxy (t :: AttTy)
pAtt = Proxy

data Att (t :: AttTy) where
  MkAtt :: KnownSymbol n => {getV :: t} -> Att '(n, t)

getP :: KnownSymbol n => Att '(n,t) -> SSymbol n
getP _ = SSymbol
