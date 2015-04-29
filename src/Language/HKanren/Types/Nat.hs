----------------------------------------------------------------------------
-- |
-- Module      :  Language.HKanren.Types.Nat
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.HKanren.Types.Nat
  ( NatF(..)
  , Nat
  , iZ
  , iS
  , int2nat
  )
where

import Data.HOrdering
import Data.HUtils
import Data.Monoid
import Data.Type.Equality
import Text.PrettyPrint.Leijen.Text ((<+>))
import qualified Text.PrettyPrint.Leijen.Text as PP

import Language.HKanren.Core (Unifiable(..), unifyTerms)
import Language.HKanren.Subst (Term, Term1, LVar, LFunctor, Equal, TypeI(..))


data Nat

data NatF :: (* -> *) -> (* -> *) where
  Z :: NatF h Nat
  S :: h Nat -> NatF h Nat

iZ :: (NatF :<: LFunctor k) => Term k Nat
iZ = inject Z

iS :: (NatF :<: LFunctor k) => Term k Nat -> Term k Nat
iS = inject . S

-- pluso :: (NatF :<: LFunctor k) => Term k Nat -> Term k Nat -> Term k Nat -> Predicate k
-- pluso x y z = do
--   x ==^ NatF n

instance (HEq h) => HEq (NatF h) where
  {-# INLINABLE heq #-}
  heq Z     Z     = True
  heq Z     (S _) = False
  heq (S _) Z     = False
  heq (S x) (S y) = heq x y

instance (HEq h) => HEqHet (NatF h) where
  {-# INLINABLE heqIx #-}
  heqIx Z     Z     = Just Refl
  heqIx Z     (S _) = Just Refl
  heqIx (S _) Z     = Just Refl
  heqIx (S _) (S _) = Just Refl

instance (HOrd h) => HOrd (NatF h) where
  {-# INLINABLE hcompare #-}
  hcompare Z     Z     = EQ
  hcompare Z     (S _) = LT
  hcompare (S _) Z     = GT
  hcompare (S x) (S y) = hcompare x y

instance (HOrd h) => HOrdHet (NatF h) where
  {-# INLINABLE hcompareIx #-}
  hcompareIx Z     Z     = HEQ
  hcompareIx Z     (S _) = HEQ
  hcompareIx (S _) Z     = HEQ
  hcompareIx (S _) (S _) = HEQ



instance HFunctorId NatF where
  hfmapId _ Z     = Z
  hfmapId f (S x) = S $ f x

instance HFoldable NatF where
  hfoldMap _ Z     = mempty
  hfoldMap f (S x) = f x

instance (HShow h) => HShow (NatF h) where
  hshowsPrec _ Z     = showString "Z"
  hshowsPrec n (S x) =
    showParen (n == 11) (showString "S " . hshowsPrec 11 x)

instance (HPretty h) => HPretty (NatF h) where
  hpretty Z     = "Z"
  hpretty (S x) = PP.parens ("S" <+> hpretty x)


instance (Unifiable (LFunctor k) k, LVar k, HFoldable (LFunctor k), HOrdHet (Type (Term1 k))) => Unifiable NatF k where
  unify Z     Z     = Just
  unify Z     (S _) = const Nothing
  unify (S _) Z     = const Nothing
  unify (S x) (S y) = unifyTerms x y


instance (ix ~ Nat) => TypeI (NatF h) ix where
  type SupportsIx (NatF h) ix = Equal ix Nat
  data Type (NatF h) idx where
    TNat :: Type (NatF h) Nat
  singType = TNat

instance HEq (Type (NatF h)) where
  {-# INLINABLE heq #-}
  heq TNat TNat = True

instance HEqHet (Type (NatF h)) where
  {-# INLINABLE heqIx #-}
  heqIx TNat TNat = Just Refl

instance HOrd (Type (NatF h)) where
  {-# INLINABLE hcompare #-}
  hcompare TNat TNat = EQ

instance HOrdHet (Type (NatF h)) where
  {-# INLINABLE hcompareIx #-}
  hcompareIx TNat TNat = {-# SCC hcompareIx_type_TInt #-} HEQ

int2nat :: forall k. (NatF :<: LFunctor k, LVar k) => Int -> Term k Nat
int2nat n
  | n < 0     = error $ "cannot convert int < 0 " ++ show n ++ " to Nat"
  | otherwise = go n
  where
    go :: Int -> Term k Nat
    go 0 = iZ
    go m = iS $ go $! m - 1
