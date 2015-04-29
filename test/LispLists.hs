{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE EmptyDataDecls            #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

module LispLists where

import Control.DeepSeq
import Data.HOrdering
import Data.HUtils
import Data.Monoid
import qualified Data.Text.Lazy as T
import Data.Type.Equality
import Language.HKanren
import qualified Language.HKanren.SafeLVar as Safe
import Language.HKanren.Types.List
import Language.HKanren.Types.Nat
import qualified Text.PrettyPrint.Leijen.Text as PP


data Atom

instance (ix ~ Atom) => TypeI (AtomF h) ix where
  type SupportsIx (AtomF h) ix = Equal ix Atom
  data Type (AtomF h) idx where
    TAtom :: Type (AtomF h) Atom
  singType = TAtom

instance HEq (Type (AtomF h)) where
  heq TAtom TAtom = True

instance HEqHet (Type (AtomF h)) where
  heqIx TAtom TAtom = Just Refl

instance HOrd (Type (AtomF h)) where
  hcompare TAtom TAtom = EQ

instance HOrdHet (Type (AtomF h)) where
  hcompareIx TAtom TAtom = HEQ

instance HNFData (Type (AtomF h)) where
  hrnf TAtom = ()


data AtomF :: (* -> *) -> (* -> *) where
  Atom :: String -> AtomF r Atom

iAtom :: (AtomF :<: LFunctor k) => String -> Term k Atom
iAtom = inject . Atom

instance (AtomF :<: LFunctor k) => Unifiable AtomF k where
  unify (Atom x) (Atom y) s
    | x == y    = Just s
    | otherwise = Nothing

instance HEq (AtomF f) where
  heq (Atom x) (Atom y) = x == y

instance HEqHet (AtomF f) where
  heqIx (Atom _) (Atom _) = Just Refl

instance HOrd (AtomF f) where
  hcompare (Atom x) (Atom y) = compare x y

instance HOrdHet (AtomF f) where
  hcompareIx (Atom _) (Atom _) = HEQ


instance HFunctorId AtomF where
  hfmapId _ (Atom n) = Atom n

instance HFunctor AtomF where
  hfmap _ (Atom n) = Atom n

instance HFoldable AtomF where
  hfoldMap _ _ = mempty

instance HShow (AtomF f) where
  hshowsPrec n (Atom str) = \xs -> showParen (n == 11) (\ys -> "Atom " ++ show str ++ ys) xs

instance HPretty (AtomF f) where
  hpretty (Atom str) = PP.text $ T.pack str

instance HNFData (AtomF h) where
  hrnf (Atom x) = rnf x

type LispTermF = ListF :+: AtomF :+: NatF
type LispVar   = Safe.LVar LispTermF
type LispTerm  = Term LispVar

