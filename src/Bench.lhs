> module Bench (
>  module Data.Type.Attribution,
>  module Data.Attribution,
>  module Data.Type.Rule,
>  module Data.Rule,
>  module Data.Attribute,
>  module Data.Type.Utils,
>  module Data.Type.Aspect,
>  module Data.Aspect
> ) where


> import Data.Type.Attribution
> import Data.Attribution
> import Data.Type.Rule
> import Data.Rule
> import Data.Attribute
> import Data.Type.Utils
> import Data.Type.Aspect
> import Data.Aspect
> import Data.Type.Grammar
> import Data.EADT
> import GHC.TypeLits
> import MiniAspectAG
> import Data.Proxy

Syntax
======

A grammar for a simple expression language:

> type G = '[ '("3add1", "E" :=> '[ 'N "E", 'N "E", 'N "E"]),
>             '("3add2", "E" :=> '[ 'N "E", 'N "E", 'N "E"]),
>             '("3add3", "E" :=> '[ 'N "E", 'N "E", 'N "E"]),
>             '("add1",  "E" :=> '[ 'N "E", 'N "E"]),
>             '("add2",  "E" :=> '[ 'N "E", 'N "E"]),
>             '("add3",  "E" :=> '[ 'N "E", 'N "E"]),
>             '("add4",  "E" :=> '[ 'N "E", 'N "E"]),
>             '("add5",  "E" :=> '[ 'N "E", 'N "E"]),
>             '("add6",  "E" :=> '[ 'N "E", 'N "E"]),
>             '("add7",  "E" :=> '[ 'N "E", 'N "E"]),
>             '("add8",  "E" :=> '[ 'N "E", 'N "E"]),
>             '("add9",  "E" :=> '[ 'N "E", 'N "E"]),
>             '("val",   "E" :=> '[ 'T Int]),
>             '("var",   "E" :=> '[ 'T String])]


> val2 = Inner @G @"E" @"val" symbolSing $ Leaf (2 :: Int) << ArgNil

> type RuleEvalAdd
>  =   '[ '[],                '[ '("eval", Int)], '[ '("eval", Int)]]
>  :-> '[ '[ '("eval", Int)], '[],                '[]]
> type RuleEvalAdd3
>  =   '[ '[],                '[ '("eval", Int)],'[ '("eval", Int)], '[ '("eval", Int)]]
>  :-> '[ '[ '("eval", Int)], '[],                '[],                '[]]



> rul_eval_add :: Rule RuleEvalAdd
> rul_eval_add = MkRule $ \inp ->
>   (MkAtt @"eval" ((inp .$ (SS SZ)) # SSymbol @"eval"
>     + (inp .$ (SS $ SS SZ)) # SSymbol @"eval")
>        :. EmptyAtt)
>   :- EmptyAtt
>   :- EmptyAtt
>   :- EmptyFam

> rul_eval_add3 :: Rule RuleEvalAdd3
> rul_eval_add3 = MkRule $ \inp ->
>   (MkAtt @"eval" ((inp .$ (SS SZ)) # SSymbol @"eval"
>     + (inp .$ (SS $ SS SZ)) # SSymbol @"eval")
>        :. EmptyAtt)
>   :- EmptyAtt
>   :- EmptyAtt
>   :- EmptyAtt
>   :- EmptyFam


> type RuleEvalVal
>   =   '[ '[],                '[ '("term", Int)]]
>   :-> '[ '[ '("eval", Int)], '[]]
> rul_eval_val :: Rule RuleEvalVal
> rul_eval_val = MkRule $ \inp ->
>   (MkAtt @"eval" ((inp .$ (SS SZ)) # SSymbol @"term") :. EmptyAtt)
>   :- EmptyAtt
>   :- EmptyFam

> type Env = [(String, Int)]

> rul_env_l = MkRule $ \(inp :: Family '[ '[ '("env", Env)], '[], '[] ]) ->
>                              EmptyAtt
>                           :- (MkAtt @"env" (inp .$ SZ # SSymbol @"env")
>                                  :. EmptyAtt)
>                           :- EmptyAtt
>                           :- EmptyFam

> rul_env_r = MkRule $ \(inp :: Family '[ '[ '("env", Env)], '[], '[] ]) ->
>                              EmptyAtt
>                           :- EmptyAtt
>                           :- (MkAtt @"env" (inp .$ SZ # SSymbol @"env")
>                                  :. EmptyAtt)
>                           :- EmptyFam

> rul_env_l3 = MkRule $ \(inp :: Family '[ '[ '("env", Env)], '[], '[] , '[]]) ->
>                              EmptyAtt
>                           :- (MkAtt @"env" (inp .$ SZ # SSymbol @"env")
>                                  :. EmptyAtt)
>                           :- EmptyAtt
>                           :- EmptyAtt
>                           :- EmptyFam

> rul_env_c3 = MkRule $ \(inp :: Family '[ '[ '("env", Env)], '[], '[] , '[]]) ->
>                              EmptyAtt
>                           :- EmptyAtt
>                           :- (MkAtt @"env" (inp .$ SZ # SSymbol @"env")
>                                  :. EmptyAtt)
>                           :- EmptyAtt
>                           :- EmptyFam

> rul_env_r3 = MkRule $ \(inp :: Family '[ '[ '("env", Env)], '[], '[] , '[]]) ->
>                              EmptyAtt
>                           :- EmptyAtt
>                           :- EmptyAtt
>                           :- (MkAtt @"env" (inp .$ SZ # SSymbol @"env")
>                                  :. EmptyAtt)
>                           :- EmptyFam

> rul_eval_var
>    = MkRule $ \(inp :: Family '[ '[ '("env", Env)], '[ '("term", String)]]) ->
>             (MkAtt @"eval" ( lookup' (inp .$ (SS SZ) # SSymbol @"term")
>                                      (inp .$ SZ # SSymbol @"env") )
>                 :. EmptyAtt)
>             :- EmptyAtt
>             :- EmptyFam
> lookup' l v = case lookup l v of Just a -> a
> dummy = MkRule $ \(inp :: Family '[ '[ '("env", Env)], '[]]) ->
>                              EmptyAtt
>                           :- EmptyAtt
>                           :- EmptyFam


> asp_eval
>    =  singAsp @"add1" rul_eval_add 
>  .:*: singAsp @"add2" rul_eval_add 
>  .:*: singAsp @"add3" rul_eval_add 
>  .:*: singAsp @"add4" rul_eval_add 
>  .:*: singAsp @"add5" rul_eval_add 
>  .:*: singAsp @"add6" rul_eval_add 
>  .:*: singAsp @"add7" rul_eval_add 
>  .:*: singAsp @"add8" rul_eval_add 
>  .:*: singAsp @"add9" rul_eval_add 
>  .:*: singAsp @"3add1" rul_eval_add3 
>  .:*: singAsp @"3add2" rul_eval_add3
>  .:*: singAsp @"3add3" rul_eval_add3 
>  .:*: singAsp @"add1" rul_env_l 
>  .:*: singAsp @"add1" rul_env_r
>  .:*: singAsp @"add2" rul_env_l 
>  .:*: singAsp @"add2" rul_env_r
>  .:*: singAsp @"add3" rul_env_l 
>  .:*: singAsp @"add3" rul_env_r
>  .:*: singAsp @"add4" rul_env_l 
>  .:*: singAsp @"add4" rul_env_r
>  .:*: singAsp @"add5" rul_env_l 
>  .:*: singAsp @"add5" rul_env_r
>  .:*: singAsp @"add6" rul_env_l 
>  .:*: singAsp @"add6" rul_env_r
>  .:*: singAsp @"add7" rul_env_l 
>  .:*: singAsp @"add7" rul_env_r
>  .:*: singAsp @"add8" rul_env_l 
>  .:*: singAsp @"add8" rul_env_r
>  .:*: singAsp @"add9" rul_env_l 
>  .:*: singAsp @"add9" rul_env_r
>  .:*: singAsp @"3add1" rul_env_l3 
>  .:*: singAsp @"3add1" rul_env_c3
>  .:*: singAsp @"3add1" rul_env_r3
>  .:*: singAsp @"3add2" rul_env_l3 
>  .:*: singAsp @"3add2" rul_env_c3
>  .:*: singAsp @"3add2" rul_env_r3
>  .:*: singAsp @"3add3" rul_env_l3 
>  .:*: singAsp @"3add3" rul_env_c3
>  .:*: singAsp @"3add3" rul_env_r3
>  .:*: singAsp @"var"   rul_eval_var
>  .:*: singAsp @"val"   rul_eval_val
>  .:*: singAsp @"val" dummy
>  .:*: EmptyAspect

> eval env e = sem (Proxy @G) (Proxy @( '[ '("E", '[ '("env", Env)], '[ '("eval", Int)])]))
>            asp_eval e (MkAtt @"env" env :. EmptyAtt) # SSymbol @"eval"


