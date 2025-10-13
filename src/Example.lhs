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


A grammar for a simple expression language:


> type G = '[ '("add", "E" :=> '[ 'N "E", 'N "E"]),
>             '("val", "E" :=> '[ 'T Int])]


`Variant :: HList (Args g nt prd) -> Variant g nt prd`
is used to build ASTs for the grammar g of the nonteminal nt,
for a production prd. It takes the Heterogeneous list of
suitable arguments. For instance the following AST represents
the expression `2`:

> val2 = Variant @G @"E" @"val" $ (2 :: Int) ::: HNil

The following, 2+2 :

> val2p2 = Variant @G @"E" @"add" $ SV val2 ::: SV val2 ::: HNil

The constructor `SV :: Variant g nt prd -> SomeVariant g nt`
hides the production index, since it is dynamic
(it cannot be decided when computing `HList (Args g nt p)`, otherwise
we would fix the shape of the AST).
