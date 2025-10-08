{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeData #-}

module Data.Type.Utils where

import GHC.TypeLits (Symbol, CmpSymbol, TypeError,
                     ErrorMessage(..))
import Data.Type.Ord
import Data.Type.Bool
import Data.Type.Equality
import Data.Kind (Constraint) --, Type)

-- | Comparison of pairs by their first component (Symbol).
type family Leq (a :: (Symbol, k)) (b :: (Symbol, k)) :: Bool where
  Leq '(x, _) '(y, _) = CmpSymbol x y == 'LT || CmpSymbol x y == 'EQ

-- | Merge two sorted lists.
type family Merge (xs :: [(Symbol,k)]) (ys :: [(Symbol,k)]) :: [(Symbol,k)] where
  Merge '[] ys = ys
  Merge xs '[] = xs
  Merge (x ': xs) (y ': ys) =
    If (Leq x y)
       (x ': Merge xs (y ': ys))
       (y ': Merge (x ': xs) ys)

-- | Split a list into two halves.
type family Split (xs :: [a]) :: ([a],[a]) where
  Split '[]       = '( '[], '[] )
  Split '[x]      = '( '[x], '[] )
  Split (x:y:xs)  = Prepend x y (Split xs)

type family Prepend (x :: a) (y :: a) (pair :: ([a],[a])) :: ([a],[a]) where
  Prepend x y '(xs,ys) = '(x ': xs, y ': ys)

-- | Projection of the first element of a pair.
type family Fst (p :: (a,b)) :: a where
  Fst '(x,_) = x

-- | Projection of the second element of a pair.
type family Snd (p :: (a,b)) :: b where
  Snd '(_,y) = y

-- | Merge sort at the type level.
type family Sort (xs :: [(Symbol,k)]) :: [(Symbol,k)] where
  Sort '[]  = '[]
  Sort '[x] = '[x]
  Sort xs   = Merge (Sort (Fst (Split xs)))
                    (Sort (Snd (Split xs)))

-- | Example input.
type Example = '[ '("c", Int), '("a", Bool), '("b", Char) ]

-- | Expected result: '[ '("a", Bool), '("b", Char), '("c", Int) ]
type Sorted = Sort Example


type family IsMapping (xs :: [(Symbol,k)]) :: Constraint where
  IsMapping '[]  = ()
  IsMapping '[t] = ()
  IsMapping ( '(l,v) ': '(l2,v2) ': xs)
    = (Compare l l2 ~ 'LT, IsMapping ( '(l2,v2) ': xs))
    

type family Orthogonal (xs :: [(Symbol,k)]) (ys :: [(Symbol,k)])
  :: Constraint where
  Orthogonal '[] ys = ()
  Orthogonal xs '[] = ()
  Orthogonal ( '(lx,vx) ': xs) ('(ly,vy) ': ys)
    = OrthogonalAux (Compare lx ly) '(lx,vx) '(ly,vy) xs ys
type family OrthogonalAux (c :: Ordering)
         (lxvx :: (Symbol,k)) (lyvy :: (Symbol,k))
         (xs :: [(Symbol,k)]) (ys :: [(Symbol,k)])
 where
  OrthogonalAux 'EQ _ _ _ _ = TypeError (Text "ERR")
  OrthogonalAux 'LT '(lx,vx) '(ly,vy) xs ys
    = Orthogonal xs ( '(ly,vy) ': ys)


-- | open, to instantiate it with different type errors
type family (l :: [(Symbol,k)]) :.|. (r :: [(Symbol,k)]) :: Constraint


type family (x :: (Symbol,k)) :<| (xs :: [(Symbol,k)]) where
  x :<| xs = Merge '[x] xs

-- | Subtyping, generic
type family SubType (l :: [(Symbol,k)]) (r :: [(Symbol,k)]) where
  SubType '[] r = ()
  SubType ( '(l,v) ': ts) ( '(l',v') ': ts')
     = SubTypeAux (Compare l l') '(l,v) '(l',v') ts ts'
  SubType (t ': ts) '[] = TypeError (Text "ERR")
type family SubTypeAux (o :: Ordering)
              (t :: (Symbol,k)) (t' :: (Symbol,k))
              (ts :: [(Symbol,k)]) (ts' :: [(Symbol,k)]) where
  SubTypeAux 'EQ _ _ ts ts' = SubType ts ts'
  SubTypeAux 'GT t t' ts ts' = SubType (t ': ts) ts'
  SubTypeAux 'LT _ _ _ _     = TypeError (Text "ERR") 

-- |  subtyping
type family (t :: k) :< (u :: k)
