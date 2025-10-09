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

type family Ext (t :: k) (u :: k) :: k
type instance Ext ('[] :: FamilyTy) ('[] :: FamilyTy) = '[]
type instance Ext (att  ': atts  :: FamilyTy) (att' ': atts' :: FamilyTy)
  = att :++ att' ': Ext atts atts' 
type instance Ext (inp :-> out) (inp' :-> out')
  = (Ext inp inp' :-> Ext out out')

-- | subtypr for families 
type instance ('[] :: FamilyTy) :< (f :: FamilyTy) = ()
type instance (attr  ': attrs  :: FamilyTy) :<
              (attr' ': attrs' :: FamilyTy) = (attr :< attr', attrs :< attrs') 

-- | subtype for rules
type instance (inp :-> out) :< (inp' :-> out') = (inp :< inp', out' :< out)

