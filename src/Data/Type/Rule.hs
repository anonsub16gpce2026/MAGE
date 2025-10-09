{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Type.Rule where

import Data.Type.Attribution
import Data.Type.Utils
import GHC.TypeLits

type FamilyTy = [AttributionTy]

infixr 4 :->
type data RuleTy = FamilyTy :-> FamilyTy

type family EmptyRuleN (n :: N) :: RuleTy where
  EmptyRuleN n = EmptyFamN n :-> EmptyFamN n
type family EmptyFamN (n :: N) :: FamilyTy where
  EmptyFamN Z = '[]
  EmptyFamN (S n) = '[] ': EmptyFamN n

type family AtN (n :: N) (s :: k) :: AttributionTy
type instance AtN Z (att ': atts :: FamilyTy) = att
type instance AtN Z ('[] :: FamilyTy) = TypeError (Text "Err:OOB")
type instance AtN (S n) (att ': atts :: FamilyTy) = AtN n atts
type instance AtN Z ((att ': _ :-> _) :: RuleTy) = att
type instance AtN (S n) ((att ': atts :-> _) :: RuleTy)
  = AtN n atts
