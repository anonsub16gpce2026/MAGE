> {-# LANGUAGE ScopedTypeVariables #-}

> module Bench2 (
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

> type RuleEvalAdd eval
>  =   '[ '[],                '[ '(eval, Int)], '[ '(eval, Int)]]
>  :-> '[ '[ '(eval, Int)], '[],                '[]]
> type RuleEvalAdd3 eval
>  =   '[ '[],                '[ '(eval, Int)],'[ '(eval, Int)], '[ '(eval, Int)]]
>  :-> '[ '[ '(eval, Int)], '[],                '[],                '[]]



> rul_eval_add :: forall eval . KnownSymbol eval => Proxy eval -> Rule (RuleEvalAdd eval)
> rul_eval_add _ = MkRule $ \inp ->
>   (MkAtt @eval ((inp .$ (SS SZ)) # SSymbol @eval
>     + (inp .$ (SS $ SS SZ)) # SSymbol @eval)
>        :. EmptyAtt)
>   :- EmptyAtt
>   :- EmptyAtt
>   :- EmptyFam

> rul_eval_add3 :: forall eval. KnownSymbol eval => Proxy eval -> Rule (RuleEvalAdd3 eval) 
> rul_eval_add3 _ = MkRule $ \inp ->
>   (MkAtt @eval ((inp .$ (SS SZ)) # SSymbol @eval
>     + (inp .$ (SS $ SS SZ)) # SSymbol @eval)
>        :. EmptyAtt)
>   :- EmptyAtt
>   :- EmptyAtt
>   :- EmptyAtt
>   :- EmptyFam


> type RuleEvalVal eval
>   =   '[ '[],                '[ '("term", Int)]]
>   :-> '[ '[ '(eval, Int)], '[]]
> rul_eval_val :: forall eval . KnownSymbol eval => Proxy eval -> Rule (RuleEvalVal eval)
> rul_eval_val _ = MkRule $ \inp ->
>   (MkAtt @eval ((inp .$ (SS SZ)) # SSymbol @"term") :. EmptyAtt)
>   :- EmptyAtt
>   :- EmptyFam

> type Env = [(String, Int)]

> rul_env_l (Proxy :: Proxy env)
>           = MkRule $ \(inp :: Family '[ '[ '(env, Env)], '[], '[] ]) ->
>                              EmptyAtt
>                           :- (MkAtt @env (inp .$ SZ # SSymbol @env)
>                                  :. EmptyAtt)
>                           :- EmptyAtt
>                           :- EmptyFam

> rul_env_r (Proxy :: Proxy env)
>          = MkRule $ \(inp :: Family '[ '[ '(env, Env)], '[], '[] ]) ->
>                              EmptyAtt
>                           :- EmptyAtt
>                           :- (MkAtt @env (inp .$ SZ # SSymbol @env)
>                                  :. EmptyAtt)
>                           :- EmptyFam

> rul_env_l3 (Proxy :: Proxy env)
>          = MkRule $ \(inp :: Family '[ '[ '(env, Env)], '[], '[] , '[]]) ->
>                              EmptyAtt
>                           :- (MkAtt @env (inp .$ SZ # SSymbol @env)
>                                  :. EmptyAtt)
>                           :- EmptyAtt
>                           :- EmptyAtt
>                           :- EmptyFam

> rul_env_c3 (Proxy :: Proxy env)
>          = MkRule $ \(inp :: Family '[ '[ '(env, Env)], '[], '[] , '[]]) ->
>                              EmptyAtt
>                           :- EmptyAtt
>                           :- (MkAtt @env (inp .$ SZ # SSymbol @env)
>                                  :. EmptyAtt)
>                           :- EmptyAtt
>                           :- EmptyFam

> rul_env_r3 (Proxy :: Proxy env)
>          = MkRule $ \(inp :: Family '[ '[ '(env, Env)], '[], '[] , '[]]) ->
>                              EmptyAtt
>                           :- EmptyAtt
>                           :- EmptyAtt
>                           :- (MkAtt @env (inp .$ SZ # SSymbol @env)
>                                  :. EmptyAtt)
>                           :- EmptyFam

> rul_eval_var (Proxy :: Proxy eval) (Proxy :: Proxy env)
>    = MkRule $ \(inp :: Family '[ '[ '(env, Env)], '[ '("term", String)]]) ->
>             (MkAtt @eval ( lookup' (inp .$ (SS SZ) # SSymbol @"term")
>                                      (inp .$ SZ # SSymbol @env) )
>                 :. EmptyAtt)
>             :- EmptyAtt
>             :- EmptyFam
> lookup' l v = case lookup l v of Just a -> a
> dummy (env :: Proxy env) = MkRule $ \(inp :: Family '[ '[ '(env, Env)], '[]]) ->
>                              EmptyAtt
>                           :- EmptyAtt
>                           :- EmptyFam

-- > asp_eval
-- >    = let penv  = Proxy @"env"
-- >          peval = Proxy @"eval"
-- >      in singAsp @"add1" (rul_eval_add peval) 
-- >  .:*: singAsp @"add2" (rul_eval_add peval)
-- >  .:*: EmptyAspect

> asp_evalp penv peval
>    =  singAsp @"add1" (rul_eval_add peval) 
>  .:*: singAsp @"add2" (rul_eval_add peval)
>  .:*: singAsp @"add3" (rul_eval_add peval)
>  .:*: singAsp @"add4" (rul_eval_add peval)
>  .:*: singAsp @"add5" (rul_eval_add peval)
>  .:*: singAsp @"add6" (rul_eval_add peval)
>  .:*: singAsp @"add7" (rul_eval_add peval)
>  .:*: singAsp @"add8" (rul_eval_add peval)
>  .:*: singAsp @"add9" (rul_eval_add peval)
>  .:*: singAsp @"3add1" (rul_eval_add3 peval)
>  .:*: singAsp @"3add2" (rul_eval_add3 peval)
>  .:*: singAsp @"3add3" (rul_eval_add3 peval)
>  .:*: singAsp @"add1" (rul_env_l penv)
>  .:*: singAsp @"add1" (rul_env_r penv)
>  .:*: singAsp @"add2" (rul_env_l penv)
>  .:*: singAsp @"add2" (rul_env_r penv)
>  .:*: singAsp @"add3" (rul_env_l  penv)
>  .:*: singAsp @"add3" (rul_env_r penv)
>  .:*: singAsp @"add4" (rul_env_l  penv)
>  .:*: singAsp @"add4" (rul_env_r penv)
>  .:*: singAsp @"add5" (rul_env_l  penv)
>  .:*: singAsp @"add5" (rul_env_r penv)
>  .:*: singAsp @"add6" (rul_env_l  penv)
>  .:*: singAsp @"add6" (rul_env_r penv)
>  .:*: singAsp @"add7" (rul_env_l  penv)
>  .:*: singAsp @"add7" (rul_env_r penv)
>  .:*: singAsp @"add8" (rul_env_l  penv)
>  .:*: singAsp @"add8" (rul_env_r penv)
>  .:*: singAsp @"add9" (rul_env_l  penv)
>  .:*: singAsp @"add9" (rul_env_r penv)
>  .:*: singAsp @"3add1" (rul_env_l3  penv)
>  .:*: singAsp @"3add1" (rul_env_c3 penv)
>  .:*: singAsp @"3add1" (rul_env_r3 penv)
>  .:*: singAsp @"3add2" (rul_env_l3  penv)
>  .:*: singAsp @"3add2" (rul_env_c3 penv)
>  .:*: singAsp @"3add2" (rul_env_r3 penv)
>  .:*: singAsp @"3add3" (rul_env_l3  penv)
>  .:*: singAsp @"3add3" (rul_env_c3 penv)
>  .:*: singAsp @"3add3" (rul_env_r3 penv)
>  .:*: singAsp @"var"   (rul_eval_var peval penv)
>  .:*: singAsp @"val"   (rul_eval_val peval)
>  .:*: singAsp @"val"   (dummy penv)
>  .:*: EmptyAspect

> eval' env e = sem (Proxy @G)
>    (Proxy @( '[ '("E", '[ '("env", Env),  '("env2", Env),  '("env3", Env), '("env4", Env),
>                           '("env5", Env), '("env6", Env),  '("env7", Env), '("env8", Env)],
>                        '[ '("eval", Int), '("eval2", Int), '("eval3", Int), '("eval4", Int),
>                           '("eval5", Int), '("eval6", Int), '("eval7", Int), '("eval8", Int)])]))
>            (asp_evalp (Proxy @"env" ) (Proxy @"eval")   .:*:
>             asp_evalp (Proxy @"env2" ) (Proxy @"eval2") .:*:
>             asp_evalp (Proxy @"env3" ) (Proxy @"eval3") .:*:
>             asp_evalp (Proxy @"env4" ) (Proxy @"eval4") .:*:
>             asp_evalp (Proxy @"env5" ) (Proxy @"eval5") .:*:
>             asp_evalp (Proxy @"env6" ) (Proxy @"eval6") .:*:
>             asp_evalp (Proxy @"env7" ) (Proxy @"eval7") .:*:
>             asp_evalp (Proxy @"env8" ) (Proxy @"eval8")   ) e
>           (MkAtt @"env" env :. MkAtt @"env2" env :.
>            MkAtt @"env3" env :. MkAtt @"env4" env :.
>            MkAtt @"env5" env :. MkAtt @"env6" env :.
>            MkAtt @"env7" env :. MkAtt @"env8" env :. EmptyAtt) # SSymbol @"eval"


