----------------------------------------------------------------------------
-- |
-- Module      :  Data.HUtils
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances  #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Data.HUtils where

import Data.HOrdering
import Data.Type.Equality

newtype HFix (f :: (* -> *) -> (* -> *)) ix =
  HFix { unHFix :: f (HFix f) ix }

data (:*:) (f :: * -> *) (g :: * -> *) ix =
  f ix :*: g ix
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

infixr 7 :*:

data (:+:) (f :: (* -> *) -> (* -> *)) (g :: (* -> *) -> (* -> *)) (e :: * -> *) ix =
    Inl (f e ix)
  | Inr (g e ix)
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

infixr 6 :+:

instance (HEq (f e), HEq (g e)) => HEq ((:+:) f g e) where
  heq (Inl x) (Inl y) = heq x y
  heq (Inr x) (Inr y) = heq x y
  heq _       _       = False

instance (HEqIx (f e), HEqIx (g e)) => HEqIx ((:+:) f g e) where
  heqIx (Inl x) (Inl y) = heqIx x y
  heqIx (Inr x) (Inr y) = heqIx x y
  heqIx _       _       = Nothing

instance (HOrd (f e), HOrd (g e)) => HOrd ((:+:) f g e) where
  hcompare (Inl x) (Inl y) = hcompare x y
  hcompare (Inr x) (Inr y) = hcompare x y
  hcompare (Inl _) (Inr _) = LT
  hcompare (Inr _) (Inl _) = GT

instance (HOrdIx (f e), HOrdIx (g e)) => HOrdIx ((:+:) f g e) where
  hcompareIx (Inl x) (Inl y) = hcompareIx x y
  hcompareIx (Inr x) (Inr y) = hcompareIx x y
  hcompareIx (Inl _) (Inr _) = HLT
  hcompareIx (Inr _) (Inl _) = HGT

type f :-> g = forall ix. f ix -> g ix
type f :=> a = forall ix. f ix -> a
type NatM m f g = forall ix. f ix -> m (g ix)

infixr 0 :->
infixr 0 :=>

class HFunctor (h :: (* -> *) -> (* -> *)) where
  hfmap :: (f :-> g) -> h f :-> h g

instance (HFunctor f, HFunctor g) => HFunctor ((:+:) f g) where
  hfmap f (Inl h)  = Inl $ hfmap f h
  hfmap f (Inr h') = Inr $ hfmap f h'

class HFoldable (h :: (* -> *) -> (* -> *)) where
  hfoldMap :: (Monoid a) => (f :=> a) -> h f :=> a

instance (HFoldable f, HFoldable g) => HFoldable ((:+:) f g) where
  hfoldMap f (Inl h)  = hfoldMap f h
  hfoldMap f (Inr h') = hfoldMap f h'

class (HFoldable h) => HTraversable (h :: (* -> *) -> (* -> *)) where
  htraverse :: (Applicative e) => NatM e f g -> NatM e (h f) (h g)

instance (HTraversable f, HTraversable g) => HTraversable ((:+:) f g) where
  htraverse f (Inl h)  = Inl <$> htraverse f h
  htraverse f (Inr h') = Inr <$> htraverse f h'


data Free f a =
    Pure a
  | Free (f (Free f a))

data HFree (f :: (* -> *) -> (* -> *)) a ix =
    HPure (a ix)
  | HFree (f (HFree f a) ix)

newtype K a b = K a
  deriving (Show, Eq, Ord)

instance (Eq a) => HEq (K a) where
  heq (K x) (K y) = x == y

instance (Eq a) => HEqIx (K a) where
  heqIx (K _) (K _) = Nothing

instance (Ord a) => HOrd (K a) where
  hcompare (K x) (K y) = compare x y

instance (Ord a) => HOrdIx (K a) where
  hcompareIx (K x) (K y) =
    case compare x y of
      LT -> HLT
      EQ -> HLT -- whatever
      GT -> HGT

type HUnit = K ()

data Some f = forall ix. Some (f ix)

instance (HEqIx f) => Eq (Some f) where
  Some x == Some y = x ==* y

instance (HOrdIx f) => Ord (Some f) where
  compare (Some x) (Some y) =
    case hcompareIx x y of
      HLT      -> LT
      HEQ Refl -> hcompare x y
      HGT      -> GT



class (HFunctor f, HFunctor g) => (f :: (* -> *) -> (* -> *)) :<: (g :: (* -> *) -> (* -> *)) where
  inj  :: f h ix -> g h ix
  proj :: g h ix -> Maybe (f h ix)

instance (HFunctor f) => f :<: f where
  inj  = id
  proj = Just

instance (HFunctor f, HFunctor g) => f :<: (f :+: g) where
  inj = Inl
  proj (Inl x) = Just x
  proj _       = Nothing

instance (HFunctor f, HFunctor g, HFunctor h, f :<: g) => f :<: (h :+: g) where
  inj = Inr . inj
  proj (Inr x) = proj x
  proj _       = Nothing

inject :: (f :<: g) => f (HFree g a) ix -> HFree g a ix
inject = HFree . inj


class HShow (h :: * -> *) where
  hshow :: h ix -> String
  hshow x = hshowsPrec 0 x []
  hshowsPrec :: Int -> h ix -> ShowS
  hshowsPrec _ x = \xs -> hshow x ++ xs

instance (HShow (f e), HShow (g e)) => HShow ((:+:) f g e) where
  hshowsPrec n (Inl x) = \xs -> showParen (n == 11) (\ys -> "Inl " ++ hshowsPrec 11 x ys) xs
  hshowsPrec n (Inr y) = \xs -> showParen (n == 11) (\ys -> "Inr " ++ hshowsPrec 11 y ys) xs

instance (HShow f, HShow g) => HShow (f :*: g) where
  hshowsPrec n (x :*: y) =
    \xs -> showParen (n == 11) (\ys -> hshowsPrec 11 x (showString " :*: " (hshowsPrec 11 y ys))) xs

instance (HShow (f (HFree f a)), HShow a) => HShow (HFree f a) where
  hshowsPrec n (HPure x) = \xs -> showParen (n == 11) (\ys -> "HPure " ++ hshowsPrec 11 x ys) xs
  hshowsPrec n (HFree f) = \xs -> showParen (n == 11) (\ys -> "HFree " ++ hshowsPrec 11 f ys) xs

instance (HShow h) => Show (Some h) where
  show (Some x)        = hshow x
  showsPrec n (Some x) = hshowsPrec n x
