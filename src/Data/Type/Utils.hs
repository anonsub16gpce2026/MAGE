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
import Data.Kind (Constraint, Type)

-- | Comparison of pairs by their first component (Symbol).
type family Leq (a :: (Symbol, k)) (b :: (Symbol, k)) :: Bool where
  Leq '(x, _) '(y, _) = CmpSymbol x y == 'LT || CmpSymbol x y == 'EQ

type family Cm (a :: (Symbol, k)) (b :: (Symbol, k)) :: Ordering where
  Cm '(x, _) '(y, _) = CmpSymbol x y 

-- | Merge two sorted lists.
-- type family Merge (xs :: [(Symbol,k)]) (ys :: [(Symbol,k)]) :: [(Symbol,k)] where
--   Merge '[] ys = ys
--   Merge xs '[] = xs
--   Merge (x ': xs) (y ': ys) =
--     If (Leq x y)
--        (x ': Merge xs (y ': ys))
--        (y ': Merge (x ': xs) ys)

type family Merge (xs :: [(Symbol,k)]) (ys :: [(Symbol,k)]) :: [(Symbol,k)] where
  Merge '[] ys = ys
  Merge xs '[] = xs
  Merge (x ': xs) (y ': ys) = MergeAux (Cm x y) (x ': xs) (y ': ys) 
type family MergeAux (c :: Ordering)
  (xs :: [(Symbol,k)]) (ys :: [(Symbol,k)]) :: [(Symbol,k)] where
  MergeAux 'LT (x ': xs) (y ': ys) = x ': Merge xs (y ': ys)
  MergeAux 'GT (x ': xs) (y ': ys) = y ': Merge (x ': xs) ys
  MergeAux 'EQ (x ': xs) (y ': ys) = Merge (x ': xs) ys -- TODO: error

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


type family Lookup (l :: Symbol) (xs :: [(Symbol,k)]):: k where
  Lookup _ '[] = TypeError (Text "ERR:Lookup")
  Lookup l ( '(l',v) ': xs) = LookupAux (Compare l l') l v xs
type family LookupAux (o :: Ordering)(l :: Symbol)
                      (v :: k)(xs :: [(Symbol,k)]) where
  LookupAux 'EQ _ v _  = v
  LookupAux 'GT l _ xs = Lookup l xs
  LookupAux 'LT _ _ _  = TypeError (Text "ERR:Lookup")

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
type family SubType (l :: [(Symbol,k)]) (r :: [(Symbol,k)]) :: Constraint
 where
  SubType '[] r = ()
  SubType ( '(l,v) ': ts) ( '(l',v') ': ts')
     = SubTypeAux (Compare l l') '(l,v) '(l',v') ts ts'
  SubType (t ': ts) '[] = TypeError (Text "ERR")
type family SubTypeAux (o :: Ordering)
              (t :: (Symbol,k)) (t' :: (Symbol,k))
              (ts :: [(Symbol,k)]) (ts' :: [(Symbol,k)]) where
  SubTypeAux 'EQ '(_, t) '(_, t') ts ts' = (Sub t t', SubType ts ts')
  SubTypeAux 'GT t t' ts ts' = SubType (t ': ts) ts'
  SubTypeAux 'LT _ _ _ _     = TypeError (Text "ERR") 

type family Sub (t :: k)(u :: k) :: Constraint
type instance Sub (t :: Type) (u :: Type) = t ~ u

-- |  subtyping
type family (t :: k) :< (u :: k) :: Constraint


type family Project (l :: [Symbol]) (xs :: [(Symbol, k)]) :: [(Symbol, k)]
 where
  Project '[] _ = '[]
  Project ( l ': ls) ( '(l', v) ': atts)
    = ProjectAux (Compare l l') l l' v ls atts
type family ProjectAux (o :: Ordering)
                       (l :: Symbol) (l' :: Symbol) (v :: k)
                       (ls :: [Symbol]) (atts :: [(Symbol, k)])
 where
  ProjectAux EQ l l' v ls atts = '(l, v) ': Project ls atts
  ProjectAux LT l l' v ls atts = Project ls ( '(l', v) ': atts)
  ProjectAux GT l l' v ls atts = Project (l ': ls) atts

type family As (l :: k) (r :: k) :: k 

type family Labels (xs :: [(Symbol, k)]) :: [Symbol] where
  Labels '[] = '[]
  Labels ( '(l,_) ':  xs) = l ': Labels xs 


data N = Z | S N

data SNat (n :: N) where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

data HList (t :: [Type]) where
  HNil :: HList '[]
  (:::) :: t -> HList l -> HList (t ': l)
infixr 5 :::

data HKList (f :: k -> Type) (l :: [k]) where
  HKNil  :: HKList f '[]
  HKCons :: f t -> HKList f ts -> HKList f (t ': ts)


type family Head (t :: [k]) where
  Head (t ': ts) = t

