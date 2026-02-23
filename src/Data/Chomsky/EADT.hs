module Data.Chomsky.EADT where


import Data.Type.Grammar
import GHC.TypeLits
import Data.Type.Ord
import Data.Kind
import Data.Type.Utils
import Data.Proxy
import Data.EADT (Args)


data EADT (g :: Grammar) (sym :: TNT) (p :: ProdName) where
  Inner :: forall g nt p q r (s1 :: TNT) (s2 :: TNT).
      -- (Args g nt p ~ '[ 'N nt1, 'N nt2],
            (KnownSymbol p, KnownSymbol q, KnownSymbol r) => 
    SSymbol p -> EADT g s1 q -> EADT g s2 r
    -> EADT g ('N nt) p
  Leaf  :: forall g t p. t  -> EADT g ('T t) p
