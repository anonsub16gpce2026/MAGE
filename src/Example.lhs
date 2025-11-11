> module Example (
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

> type G = '[ '("add", "E" :=> '[ 'N "E", 'N "E"]),
>             '("val", "E" :=> '[ 'T Int])]


`Variant :: HList (Args g nt prd) -> Variant g nt prd`
is used to build ASTs for the grammar g of the nonteminal nt,
for a production prd. It takes the Heterogeneous list of
suitable arguments. For instance the following AST represents
the expression `2`:

> val2 = Inner @G @"E" @"val" symbolSing $ Leaf (2 :: Int) << ArgNil

The following, 2+2 :

> val2p2 = Inner @G @"E" @"add" symbolSing $ val2 <<  val2 <<  ArgNil

The constructor `SV :: Variant g nt prd -> SomeVariant g nt`
hides the production index, since it is dynamic
(it cannot be decided when computing `HList (Args g nt p)`, otherwise
we would fix the shape of the AST).

Semantics
=========

We use the attribute "eval" of type Int to denote the value of the expression.
Let us build a rule to compute "eval" at "add".
Its type states that it depends on eval at the first and second child,
and computes eval at the father:

> type RuleEvalAdd
>   =  '[ '[],                '[ '("eval", Int)], '[ '("eval", Int)]]
>  :-> '[ '[ '("eval", Int)], '[],                '[]]

The proper rule:

> rul_eval_add :: Rule RuleEvalAdd
> rul_eval_add = MkRule $ \inp ->
>   (MkAtt @"eval" ((inp .$ (SS SZ)) # SSymbol @"eval"
>     + (inp .$ (SS $ SS SZ)) # SSymbol @"eval")
>        :. EmptyAtt)
>   :- EmptyAtt
>   :- EmptyAtt
>   :- EmptyFam

The rule is straightforward to implement, it lookups the values in the
input family and builds the output family. It is cumbersome to read,
this is fixed by building a set of combinators as we do in AspectAG.
For this document, the important thing to consider is how rules are
combined, not how they are built.

> type RuleEvalVal
>   =   '[ '[],                '[ '("term", Int)]]
>   :-> '[ '[ '("eval", Int)], '[]]
> rul_eval_val :: Rule RuleEvalVal
> rul_eval_val = MkRule $ \inp ->
>   (MkAtt @"eval" ((inp .$ (SS SZ)) # SSymbol @"term") :. EmptyAtt)
>   :- EmptyAtt
>   :- EmptyFam

The following Aspect encodes the evaluation semantics. 

> asp_evalG =  singAsp @"add" rul_eval_add
>         .:*: singAsp @"val" rul_eval_val
>         .:*: EmptyAspect

For the grammar `G`, `asp_eval` is well-formed if we consider
S("E") = "eval", S(Int) = "term" and no inherited attributes.

Let us define a schema:

> a_eval = Proxy @( '[ '("E", '[], '[ '("eval", Int)])])

ant then the corresponding evaluator:

> evalG e = sem (Proxy @G) a_eval asp_evalG e EmptyAtt # SSymbol @"eval"



Syntax extension
================
Let us extend the grammar G:

> type H = AddProd '("var", "E" :=> '[ 'T String])  G

We can build the semantics where variables are zero-valued:

> asp_evalH = singAsp @"var" rul_eval_var .:*: asp_evalG
>   where rul_eval_var
>           = MkRule $ \(inp :: Family ['[], '[ '("term", String)]]) ->
>             (MkAtt @"eval" (0::Int) :. EmptyAtt)
>             :- EmptyAtt
>             :- EmptyFam


And then building the new evaluator

> evalH e = sem (Proxy @H) a_eval asp_evalH e EmptyAtt # SSymbol @"eval"


Semantics extension
===================

> type Env = [(String, Int)]

> asp_evalenvH
>    =  singAsp @"add" rul_env_l 
>  .:*: singAsp @"add" rul_env_r
>  .:*: singAsp @"var" rul_eval_var
>  .:*: singAsp @"val" dummy
>  .:*: asp_evalG

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

> rul_eval_var
>    = MkRule $ \(inp :: Family '[ '[ '("env", Env)], '[ '("term", String)]]) ->
>             (MkAtt @"eval" ( lookup' (inp .$ (SS SZ) # SSymbol @"term")
>                                      (inp .$ SZ # SSymbol @"env") )
>                 :. EmptyAtt)
>             :- EmptyAtt
>             :- EmptyFam

> dummy = MkRule $ \(inp :: Family '[ '[ '("env", Env)], '[]]) ->
>                              EmptyAtt
>                           :- EmptyAtt
>                           :- EmptyFam

> lookup' l v = case lookup l v of Just a -> a

> evalenvH env e
>    = sem (Proxy @H) (Proxy @( '[ '("E", '[ '("env", Env)], '[ '("eval", Int)])]))
>         asp_evalenvH e (MkAtt @"env" env :. EmptyAtt) # SSymbol @"eval"


> val2H    = Inner @H @"E" @"val" symbolSing $ Leaf (2 :: Int) << ArgNil
> val2p2H  = Inner @H @"E" @"add" symbolSing $ val2H <<  val2H <<  ArgNil
> val2p2px = Inner @H @"E" @"add" symbolSing $ val2p2H << x <<  ArgNil
>   where x = Inner @H @"E" @"var" symbolSing $ Leaf "x" << ArgNil

