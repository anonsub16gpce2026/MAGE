module Data.Grammar where

import Data.Type.Grammar
import GHC.TypeLits
import Data.Proxy
import Data.Type.Utils

data SGSyms (tnt :: [TNT]) where
  GSymsNil :: SGSyms '[]
  ConsNT :: SSymbol nt -> SGSyms tnt -> SGSyms ('N nt ': tnt)
  ConsT  :: Proxy t -> SGSyms tnt -> SGSyms ('T t ': tnt)

data SProd (p :: Prod) where
  SProd :: SSymbol nt -> SGSyms tnt -> SProd (nt :=> tnt)

type SGram (t :: [Prod]) = HKList SProd
