----------------------------------------------------------------------------
-- |
-- Module      :  Language.HKanren.Types.List
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.HKanren.Types.List
  ( List
  , ListF(..)
  , list
  , ilist
  )
where

import Control.Monad
import Data.HOrdering
import Data.HUtils
import Data.Monoid
import Data.Type.Equality

import Language.HKanren.Core (Unifiable(..), unifyTerms)
import Language.HKanren.Subst (Term, TypeI(..))


data List ix

type family IsList (ix :: *) :: Bool where
  IsList (List ix) = 'True
  IsList b         = 'False

instance (TypeI h ix', List ix' ~ ix) => TypeI (ListF h) ix where
  type SupportsIx (ListF h) ix = IsList ix
  data Type (ListF h) idx where
    TList :: Type h ix' -> Type (ListF h) (List ix')
  singType = TList singType

instance (HEq (Type h)) => HEq (Type (ListF h)) where
  heq (TList x) (TList y) = heq x y

instance (HEqHet (Type h)) => HEqHet (Type (ListF h)) where
  heqIx (TList x) (TList y) =
    case heqIx x y of
      Just Refl -> Just Refl
      Nothing   -> Nothing

instance (HOrd (Type h)) => HOrd (Type (ListF h)) where
  hcompare (TList x) (TList y) = hcompare x y

instance (HOrdHet (Type h)) => HOrdHet (Type (ListF h)) where
  hcompareIx (TList x) (TList y) =
    case hcompareIx x y of
      HLT      -> HLT
      HEQ Refl -> HEQ Refl
      HGT      -> HGT


data ListF :: (* -> *) -> (* -> *) where
  Nil  :: (TypeI r ix) => ListF r (List ix)
  Cons :: (TypeI r ix) => r ix -> r (List ix) -> ListF r (List ix)

typeOfElems :: (TypeI f ix) => p f (List ix) -> Type f ix
typeOfElems _ = singType

instance (HFoldable h, HOrdHet (Type (h (Term h))), Unifiable h h) => Unifiable ListF h where
  unify Nil         Nil         = return
  unify (Cons x xs) (Cons y ys) =
    unifyTerms x y >=> unifyTerms xs ys
  unify _ _ = const Nothing

instance (HEq f) => HEq (ListF f) where
  heq Nil         Nil         = True
  heq (Cons x xs) (Cons y ys) = heq x y && heq xs ys
  heq _           _           = False

instance (HEqHet (Type f)) => HEqHet (ListF f) where
  heqIx :: forall ix ix'. ListF f ix -> ListF f ix' -> Maybe (ix :~: ix')
  heqIx x@Nil        y@Nil =
    case heqIx (typeOfElems x) (typeOfElems y) of
      Just Refl -> Just Refl
      Nothing   -> Nothing
  heqIx x@Nil        y@(Cons _ _) =
    case heqIx (typeOfElems x) (typeOfElems y) of
      Just Refl -> Just Refl
      Nothing   -> Nothing
  heqIx x@(Cons _ _) y@Nil =
    case heqIx (typeOfElems x) (typeOfElems y) of
      Just Refl -> Just Refl
      Nothing   -> Nothing
  heqIx x@(Cons _ _) y@(Cons _ _) =
    case heqIx (typeOfElems x) (typeOfElems y) of
      Just Refl -> Just Refl
      Nothing   -> Nothing

instance (HOrd f) => HOrd (ListF f) where
  hcompare Nil         Nil         = EQ
  hcompare Nil         (Cons _ _)  = LT
  hcompare (Cons _ _)  Nil         = GT
  hcompare (Cons x xs) (Cons y ys) = hcompare x y <> hcompare xs ys

instance (HOrdHet (Type f)) => HOrdHet (ListF f) where
  hcompareIx x@Nil        y@Nil        =
    case hcompareIx (typeOfElems x) (typeOfElems y) of
      HLT      -> HLT
      HEQ Refl -> HEQ Refl
      HGT      -> HGT
  hcompareIx x@Nil        y@(Cons _ _) =
    case hcompareIx (typeOfElems x) (typeOfElems y) of
      HLT      -> HLT
      HEQ Refl -> HEQ Refl
      HGT      -> HGT
  hcompareIx x@(Cons _ _) y@Nil        =
    case hcompareIx (typeOfElems x) (typeOfElems y) of
      HLT      -> HLT
      HEQ Refl -> HEQ Refl
      HGT      -> HGT
  hcompareIx x@(Cons _ _) y@(Cons _ _) =
    case hcompareIx (typeOfElems x) (typeOfElems y) of
      HLT      -> HLT
      HEQ Refl -> HEQ Refl
      HGT      -> HGT

instance HFunctorId ListF where
  hfmapId _ Nil         = Nil
  hfmapId f (Cons x xs) = Cons (f x) (f xs)

-- instance HFunctor ListF where
--   hfmap _ (Nil t)       = Nil t
--   hfmap f (Cons t x xs) = Cons t (f x) (f xs)

instance HFoldable ListF where
  hfoldMap _ Nil         = mempty
  hfoldMap f (Cons x xs) = f x <> f xs

instance (HShow f) => HShow (ListF f) where
  hshowsPrec _ Nil         = \xs -> "Nil" ++ xs
  hshowsPrec n (Cons x xs) =
    \ys -> showParen (n == 11) (\zs -> "Cons " ++ hshowsPrec 11 x (showChar ' ' $ hshowsPrec 11 xs zs)) ys


list :: (ListF :<: h, TypeI (h (Term h)) ix) => [h (Term h) ix] -> h (Term h) (List ix)
list = foldr (\x y -> inj $ Cons (HFree x) (HFree y)) (inj Nil)

ilist :: (ListF :<: h, TypeI (h (Term h)) ix) => [h (Term h) ix] -> Term h (List ix)
ilist = HFree . list
