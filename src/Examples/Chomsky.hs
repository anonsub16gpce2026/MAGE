{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RebindableSyntax #-}


module Examples.Chomsky where

import Control.Monad.Reader
import Data.Rule
import Data.Type.Rule
import Control.Monad qualified as CM
import Data.Attribution
import Data.Attribute
import Data.Type.Grammar
import Data.Type.Aspect
import Data.Aspect
import Data.EADT

import Data.EEADT qualified as E

import GHC.TypeLits
import Data.Proxy

import Prelude hiding ((>>), (>>=), return)
import Control.IMonad
import MiniAspectAG

import Chomsky.MiniAspectAG qualified as CAG
import Data.Chomsky.EADT qualified as CEADT
{---------
Some combinators for Grammars in Chomsky Normal Form: Productions
rewrite either to a terminal, or to a list of two non-terminals
----------}

-- combinators
(>>=) = (>>=.)
(>>)  = (>>.)

return = preturn @(Reader (Family '[ '[], '[], '[]]))


at1 :: forall att t. Reader (Family ([ '[], '[ '(att, t)], '[]])) t
at1 = CM.liftM (\(_ :- (MkAtt t :. _) :- _) -> t) ask

at2 :: forall att t. Reader (Family ([ '[], '[], '[ '(att, t)]])) t
at2 = CM.liftM (\(_ :- _ :- (MkAtt t :. _) :- _) -> t) ask


atchi :: forall t. Reader (Family ('[ '[], '[ '("term", t)]])) t
atchi = CM.liftM (\(_ :- (MkAtt t :. _) :- _) -> t) ask

syn2 :: forall att t f . KnownSymbol att
   => Reader (Family f) t -> Rule (f :-> [ '[ '(att,t)], '[], '[]])
syn2 f
  = syndef2 . runReader $ f
syndef2 f
  = MkRule $ \inp -> ( singAttr (f inp) :- EmptyAtt :- EmptyAtt :- EmptyFam) 

syn1 :: forall att t f . KnownSymbol att
   => Reader (Family f) t -> Rule (f :-> [ '[ '(att,t)], '[]])
syn1 f
  = syndef1 . runReader $ f
syndef1 f
  = MkRule $ \inp -> ( singAttr (f inp) :- EmptyAtt :- EmptyFam) 

-- Example

type G = '[ '("add", "E" :=> '[ 'N "E", 'N "E"]),
            '("val", "E" :=> '[ 'T Int])]

val2 = Inner @G @"E" @"val" symbolSing $ Leaf (2 :: Int) << ArgNil
val2p2 = Inner @G @"E" @"add" symbolSing $ val2 <<  val2 << ArgNil

add_eval = syn2 @"eval" @Int $ do l <- at1 @"eval" @Int
                                  r <- at2 @"eval" @Int
                                  return $ l + r
val_eval = syn1 @"eval" $ atchi @Int

asp_evalG =  singAsp @"add" add_eval
        .:*: singAsp @"val" val_eval
        .:*: EmptyAspect

a_eval = Proxy @( '[ '("E", '[], '[ '("eval", Int)])])
evalG e = sem (Proxy @G) a_eval asp_evalG e EmptyAtt # SSymbol @"eval"

-- example with explicit indexes

val2' = CEADT.Leaf @G @Int @"val" (2 :: Int)
val2p2' = CEADT.Inner @G @"E" @"add" symbolSing val2' val2'


