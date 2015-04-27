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

module Language.HKanren.Types.List
  ( List
  , ListF(..)
  , iNil
  , iCons
  , list
  , ReifyList(..)
  , reifyList
  )
where

import Control.Monad
import Data.HOrdering
import Data.HUtils
import Data.Monoid
import Data.Singletons
import Data.Singletons.Prelude.Bool
import Data.Type.Equality
import Text.PrettyPrint.Leijen.Text ((<+>))

import Language.HKanren.Core (Unifiable(..), unifyTerms)
import Language.HKanren.Subst (Term, Term1, LVar, LFunctor, TypeI(..))


data List ix

type family IsList (ix :: *) :: Bool where
  IsList (List a) = 'True
  IsList b        = 'False

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
      HLT -> HLT
      HEQ -> HEQ
      HGT -> HGT

instance (HNFData (Type h)) => HNFData (Type (ListF h)) where
  hrnf (TList x) = hrnf x


data ListF :: (* -> *) -> (* -> *) where
  Nil  :: (TypeI h ix) => ListF h (List ix)
  Cons :: (TypeI h ix) => h ix -> h (List ix) -> ListF h (List ix)

iNil :: (TypeI (Term k) ix, ListF :<: LFunctor k, LVar k) => Term k (List ix)
iNil = inject Nil

iCons :: (TypeI (Term k) ix, ListF :<: LFunctor k, LVar k) => Term k ix -> Term k (List ix) -> Term k (List ix)
iCons x xs = inject $ Cons x xs

typeOfElems :: (TypeI h ix) => p h (List ix) -> Type h ix
typeOfElems _ = singType

instance (HFoldable (LFunctor k), HOrdHet (Type (Term1 k)), LVar k, Unifiable (LFunctor k) k) => Unifiable ListF k where
  unify Nil         Nil         = return
  unify (Cons x xs) (Cons y ys) =
    unifyTerms x y >=> unifyTerms xs ys
  unify _ _ = const Nothing

instance (HEq h) => HEq (ListF h) where
  heq Nil         Nil         = True
  heq (Cons x xs) (Cons y ys) = heq x y && heq xs ys
  heq _           _           = False

instance (HEq h, HEqHet (Type h)) => HEqHet (ListF h) where
  heqIx :: forall ix ix'. ListF h ix -> ListF h ix' -> Maybe (ix :~: ix')
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

instance (HOrd h) => HOrd (ListF h) where
  hcompare Nil         Nil         = EQ
  hcompare Nil         (Cons _ _)  = LT
  hcompare (Cons _ _)  Nil         = GT
  hcompare (Cons x xs) (Cons y ys) = hcompare x y <> hcompare xs ys

instance (HEq h, HOrd h, HOrdHet (Type h)) => HOrdHet (ListF h) where
  hcompareIx x@Nil        y@Nil        =
    case hcompareIx (typeOfElems x) (typeOfElems y) of
      HLT -> HLT
      HEQ -> HEQ
      HGT -> HGT
  hcompareIx x@Nil        y@(Cons _ _) =
    case hcompareIx (typeOfElems x) (typeOfElems y) of
      HLT -> HLT
      HEQ -> HEQ
      HGT -> HGT
  hcompareIx x@(Cons _ _) y@Nil        =
    case hcompareIx (typeOfElems x) (typeOfElems y) of
      HLT -> HLT
      HEQ -> HEQ
      HGT -> HGT
  hcompareIx x@(Cons _ _) y@(Cons _ _) =
    case hcompareIx (typeOfElems x) (typeOfElems y) of
      HLT -> HLT
      HEQ -> HEQ
      HGT -> HGT

instance HFunctorId ListF where
  hfmapId _ Nil         = Nil
  hfmapId f (Cons x xs) = Cons (f x) (f xs)

-- instance HFunctor ListF where
--   hfmap _ (Nil t)       = Nil t
--   hfmap f (Cons t x xs) = Cons t (f x) (f xs)

instance HFoldable ListF where
  hfoldMap _ Nil         = mempty
  hfoldMap f (Cons x xs) = f x <> f xs

instance (HShow h) => HShow (ListF h) where
  hshowsPrec _ Nil         = \xs -> "Nil" ++ xs
  hshowsPrec n (Cons x xs) =
    \ys -> showParen (n == 11) (\zs -> "Cons " ++ hshowsPrec 11 x (showChar ' ' $ hshowsPrec 11 xs zs)) ys

instance (HPretty h) => HPretty (ListF h) where
  hpretty Nil = "Nil"
  hpretty (Cons x xs) = hpretty x <+> "::" <+> hpretty xs

instance (HNFData h) => HNFData (ListF h) where
  hrnf Nil = ()
  hrnf (Cons x xs) = hrnf x `seq` hrnf xs


list :: (ListF :<: LFunctor k, TypeI (Term k) ix, LVar k) => [Term k ix] -> Term k (List ix)
list = foldr (\x y -> iCons x y) iNil

type family CanReifyList h f where
  CanReifyList (ListF f)     f = 'True
  CanReifyList ((:+:) f g r) h = CanReifyList (f r) h :|| CanReifyList (g r) h
  CanReifyList (HFree f a)   h = CanReifyList (f (HFree f a)) h
  CanReifyList a             b = 'False

class ReifyList (h :: * -> *) (f :: * -> *) where
  reifyList' :: h (List ix) -> [f ix]

instance (ReifyList f f) => ReifyList (ListF f) f where
  reifyList' Nil         = []
  reifyList' (Cons x xs) = x : reifyList' xs

instance (If (CanReifyList (f r) h) (ReifyList (f r) h) (ReifyList (g r) h), SingI (CanReifyList (f r) h)) => ReifyList ((:+:) f g r) h where
  reifyList' z =
    case sing :: SBool (CanReifyList (f r) h) of
      STrue  ->
        case z of
          Inl x -> reifyList' x
          Inr _ -> error "List.hs: reifyList: impossible case"
      SFalse ->
        case z of
          Inl _ -> error "List.hs: reifyList: impossible case"
          Inr y -> reifyList' y

instance (ReifyList (f (HFree f a)) h) => ReifyList (HFree f a) h where
  reifyList' (HPure _) = []
  reifyList' (HFree x) = reifyList' x

reifyList :: (ReifyList h h) => h (List ix) -> [h ix]
reifyList = reifyList'
