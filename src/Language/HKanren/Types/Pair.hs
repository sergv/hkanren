----------------------------------------------------------------------------
-- |
-- Module      :  Language.HKanren.Types.Pair
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

module Language.HKanren.Types.Pair
  ( Pair
  , PairF(..)
  , iPair
  )
where

import Control.Monad
import Data.HOrdering
import Data.HUtils
import Data.Monoid
import Data.Type.Equality
import Text.PrettyPrint.Leijen.Text ((<+>), parens)

import Language.HKanren.Core (Unifiable(..), unifyTerms)
import Language.HKanren.Subst (Term, Term1, LVar, LFunctor, TypeI(..))


data Pair a b

type family IsPair (ix :: *) :: Bool where
  IsPair (Pair a b) = 'True
  IsPair b          = 'False

instance (TypeI h a, TypeI h b, Pair a b ~ ix) => TypeI (PairF h) ix where
  type SupportsIx (PairF h) ix = IsPair ix
  data Type (PairF h) idx where
    TPair :: Type h a -> Type h b -> Type (PairF h) (Pair a b)
  singType = TPair singType singType

instance (HEq (Type h)) => HEq (Type (PairF h)) where
  heq (TPair x y) (TPair x' y') = heq x x' && heq y y'

instance (HEqHet (Type h)) => HEqHet (Type (PairF h)) where
  heqIx (TPair x y) (TPair x' y') =
    case heqIx x x' of
      Just Refl ->
        case heqIx y y' of
          Just Refl -> Just Refl
          Nothing -> Nothing
      Nothing -> Nothing

instance (HOrd (Type h)) => HOrd (Type (PairF h)) where
  hcompare (TPair x y) (TPair x' y') = hcompare x x' <> hcompare y y'

instance (HOrdHet (Type h)) => HOrdHet (Type (PairF h)) where
  hcompareIx (TPair x y) (TPair x' y') =
    case hcompareIx x x' of
      HLT -> HLT
      HEQ ->
        case hcompareIx y y' of
          HLT -> HLT
          HEQ -> HEQ
          HGT -> HGT
      HGT -> HGT

instance (HNFData (Type h)) => HNFData (Type (PairF h)) where
  hrnf (TPair x y) = hrnf x `seq` hrnf y

data PairF :: (* -> *) -> (* -> *) where
  Pair :: (TypeI h ix, TypeI h ix') => h ix -> h ix' -> PairF h (Pair ix ix')

iPair :: (TypeI (Term k) ix, TypeI (Term k) ix', PairF :<: LFunctor k)
      => Term k ix -> Term k ix' -> Term k (Pair ix ix')
iPair x y = inject $ Pair x y

instance (HFoldable (LFunctor k), HOrdHet (Type (Term1 k)), LVar k, Unifiable (LFunctor k) k) => Unifiable PairF k where
  unify (Pair x y) (Pair x' y') =
    unifyTerms x x' >=> unifyTerms y y'

instance (HEq h) => HEq (PairF h) where
  heq (Pair x y) (Pair x' y') = heq x x' && heq y y'

instance (HEqHet h) => HEqHet (PairF h) where
  heqIx (Pair x y) (Pair x' y') =
    case heqIx x x' of
      Just Refl ->
        case heqIx y y' of
          Just Refl -> Just Refl
          Nothing -> Nothing
      Nothing -> Nothing

instance (HOrd h) => HOrd (PairF h) where
  hcompare (Pair x y) (Pair x' y') = hcompare x x' <> hcompare y y'

instance (HOrdHet h) => HOrdHet (PairF h) where
  hcompareIx (Pair x y) (Pair x' y') =
    case hcompareIx x x' of
      HLT -> HLT
      HEQ ->
        case hcompareIx y y' of
          HLT -> HLT
          HEQ -> HEQ
          HGT -> HGT
      HGT -> HGT

instance HFunctorId PairF where
  hfmapId f (Pair x y) = Pair (f x) (f y)

instance HFoldable PairF where
  hfoldMap f (Pair x y) = f x <> f y

instance (HShow h) => HShow (PairF h) where
  hshowsPrec n (Pair x y) =
    showParen (n == 11) (showString "Pair " . hshowsPrec 11 x . showChar ' ' . hshowsPrec 11 y)

instance (HPretty h) => HPretty (PairF h) where
  hpretty (Pair x y) = parens (hpretty x <> "," <+> hpretty y)

instance (HNFData h) => HNFData (PairF h) where
  hrnf (Pair x y) = hrnf x `seq` hrnf y



