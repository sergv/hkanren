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

{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

{-# LANGUAGE OverlappingInstances #-}

module Data.HUtils where

import Control.Applicative
import Data.Monoid

import Data.HOrdering

import Text.PrettyPrint.Leijen.Text (Pretty, Doc)
import qualified Text.PrettyPrint.Leijen.Text as PP

newtype HFix (f :: (* -> *) -> (* -> *)) ix =
  HFix { unHFix :: f (HFix f) ix }

deriving instance (HEq (f (HFix f))) => HEq (HFix f)
deriving instance (HEqHet (f (HFix f))) => HEqHet (HFix f)
deriving instance (HOrd (f (HFix f))) => HOrd (HFix f)
deriving instance (HOrdHet (f (HFix f))) => HOrdHet (HFix f)

hcata :: (HFunctor f) => (f a :-> a) -> HFix f :-> a
hcata alg = alg . hfmap (hcata alg) . unHFix

data (:*:) (f :: * -> *) (g :: * -> *) ix =
  f ix :*: g ix

infixr 7 :*:

data (:+:) (f :: (* -> *) -> (* -> *)) (g :: (* -> *) -> (* -> *)) (r :: * -> *) ix =
    Inl (f r ix)
  | Inr (g r ix)

infixr 6 :+:

instance (HEq (f r), HEq (g r)) => HEq ((:+:) f g r) where
  heq (Inl x) (Inl y) = heq x y
  heq (Inr x) (Inr y) = heq x y
  heq _       _       = False

instance (HEqHet (f r), HEqHet (g r)) => HEqHet ((:+:) f g r) where
  heqIx (Inl x) (Inl y) = heqIx x y
  heqIx (Inr x) (Inr y) = heqIx x y
  heqIx _       _       = Nothing

instance (HOrd (f r), HOrd (g r)) => HOrd ((:+:) f g r) where
  hcompare (Inl x) (Inl y) = hcompare x y
  hcompare (Inr x) (Inr y) = hcompare x y
  hcompare (Inl _) (Inr _) = LT
  hcompare (Inr _) (Inl _) = GT

instance (HOrdHet (f r), HOrdHet (g r)) => HOrdHet ((:+:) f g r) where
  hcompareIx (Inl x) (Inl y) = hcompareIx x y
  hcompareIx (Inr x) (Inr y) = hcompareIx x y
  hcompareIx (Inl _) (Inr _) = HLT
  hcompareIx (Inr _) (Inl _) = HGT

instance (HShow (f r), HShow (g r)) => Show ((:+:) f g r ix) where
  showsPrec n (Inl x) = showParen (n == 11) (showString "Inl " . hshowsPrec 11 x)
  showsPrec n (Inr y) = showParen (n == 11) (showString "Inr " . hshowsPrec 11 y)

type f :-> g = forall ix. f ix -> g ix
type f :=> a = forall ix. f ix -> a
type NatM m f g = forall ix. f ix -> m (g ix)

infixr 0 :->
infixr 0 :=>

class HFunctorId (h :: (* -> *) -> (* -> *)) where
  hfmapId :: (f :-> f) -> h f :-> h f

instance (HFunctorId f, HFunctorId g) => HFunctorId ((:+:) f g) where
  hfmapId f (Inl h)  = Inl $ hfmapId f h
  hfmapId f (Inr h') = Inr $ hfmapId f h'

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

data HFree (f :: (* -> *) -> (* -> *)) (a :: * -> *) ix =
    HPure (a ix)
  | HFree (f (HFree f a) ix)

instance (HEq (f (HFree f a)), HEq a) => HEq (HFree f a) where
  heq (HPure x) (HPure y) = heq x y
  heq (HFree x) (HFree y) = heq x y
  heq _         _         = False

instance (HEqHet (f (HFree f a)), HEqHet a) => HEqHet (HFree f a) where
  heqIx (HPure x) (HPure y) = heqIx x y
  heqIx (HFree x) (HFree y) = heqIx x y
  heqIx _         _         = Nothing

instance (HOrd (f (HFree f a)), HOrd a) => HOrd (HFree f a) where
  hcompare (HPure x) (HPure y) = hcompare x y
  hcompare (HPure _) (HFree _) = LT
  hcompare (HFree _) (HPure _) = GT
  hcompare (HFree x) (HFree y) = hcompare x y

instance (HOrdHet (f (HFree f a)), HOrdHet a) => HOrdHet (HFree f a) where
  hcompareIx (HPure x) (HPure y) = hcompareIx x y
  hcompareIx (HPure _) (HFree _) = HLT
  hcompareIx (HFree _) (HPure _) = HGT
  hcompareIx (HFree x) (HFree y) = hcompareIx x y

instance (HShow (f (HFree f a)), HShow a) => Show (HFree f a ix) where
  showsPrec n (HPure x) = showParen (n == 11) (showString "HPure " . hshowsPrec 11 x)
  showsPrec n (HFree y) = showParen (n == 11) (showString "HPure " . hshowsPrec 11 y)

newtype K a b = K a
  deriving (Show, Eq, Ord)

instance (Eq a) => HEq (K a) where
  heq (K x) (K y) = x == y

instance (Eq a) => HEqHet (K a) where
  heqIx (K _) (K _) = Nothing

instance (Ord a) => HOrd (K a) where
  hcompare (K x) (K y) = compare x y

instance (Ord a) => HOrdHet (K a) where
  hcompareIx (K x) (K y) =
    case compare x y of
      LT -> HLT
      EQ -> HLT -- whatever
      GT -> HGT

type HUnit = K ()

data Some f = forall ix. Some (f ix)

instance (HEq f, HEqHet f) => Eq (Some f) where
  {-# INLINABLE (==) #-}
  Some x == Some y = x ==* y

instance (HOrd f, HOrdHet f) => Ord (Some f) where
  {-# INLINABLE compare #-}
  compare (Some x) (Some y) =
    case hcompareIx x y of
      HLT -> LT
      HEQ -> hcompare x y
      HGT -> GT



class (f :: (* -> *) -> (* -> *)) :<: (g :: (* -> *) -> (* -> *)) where
  inj  :: f h ix -> g h ix
  proj :: g h ix -> Maybe (f h ix)

instance f :<: f where
  inj  = id
  proj = Just

-- {- # OVERLAPS #-}
instance  f :<: (f :+: g) where
  inj = Inl
  proj (Inl x) = Just x
  proj _       = Nothing

-- {- # OVERLAPS #-}
instance  (f :<: g) => f :<: (h :+: g) where
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

instance (HShow (f r), HShow (g r)) => HShow ((:+:) f g r) where
  hshowsPrec n (Inl x) = showParen (n == 11) (showString "Inl " . hshowsPrec 11 x)
  hshowsPrec n (Inr y) = showParen (n == 11) (showString "Inr " . hshowsPrec 11 y)

instance (HShow f, HShow g) => HShow (f :*: g) where
  hshowsPrec n (x :*: y) =
    \xs -> showParen (n == 11) (\ys -> hshowsPrec 11 x (showString " :*: " (hshowsPrec 11 y ys))) xs

instance (HShow (f (HFree f a)), HShow a) => HShow (HFree f a) where
  hshowsPrec n (HPure x) = showParen (n == 11) (showString "HPure " . hshowsPrec 11 x)
  hshowsPrec n (HFree f) = showParen (n == 11) (showString "HFree " . hshowsPrec 11 f)

instance (HShow h) => Show (Some h) where
  show (Some x)        = hshow x
  showsPrec n (Some x) = hshowsPrec n x


class HPretty (h :: * -> *) where
  hpretty :: h ix -> Doc

instance (HPretty h) => Pretty (Some h) where
  pretty (Some x) = hpretty x

instance (HPretty (f r), HPretty (g r)) => HPretty ((:+:) f g r) where
  hpretty (Inl x) = hpretty x
  hpretty (Inr y) = hpretty y

instance (HPretty f, HPretty g) => HPretty (f :*: g) where
  hpretty (x :*: y) = hpretty x PP.<+> ":*:" PP.<+> hpretty y

instance (HPretty (f (HFree f a)), HPretty a) => HPretty (HFree f a) where
  hpretty (HPure x) = hpretty x
  hpretty (HFree f) = hpretty f
