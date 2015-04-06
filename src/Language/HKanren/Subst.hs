----------------------------------------------------------------------------
-- |
-- Module      :  Language.DSKanren.Subst
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.HKanren.Subst
  ( Subst
  , extend
  , lookup
  , lookupVar
  -- , delete -- TODO
  , domain
  , empty
  , LVar
  , mkLVar
  -- , suc
  -- , suc'
  , Term
  , ClosedTerm
  )
where

import Data.HMap (HMap)
import qualified Data.HMap as HM
import Data.HOrdering
import Data.HUtils
import Data.Monoid
import Data.Type.Equality

import Prelude hiding (lookup)

-- | Logic variable.
data LVar (f :: (* -> *) -> (* -> *)) ix = LVar Integer (f HUnit ix)
  -- deriving (Show, Eq, Ord)

instance (HEq (h HUnit)) => HEq (LVar h) where
  heq (LVar n x) (LVar m y) = n == m && heq x y

instance (HOrdIx (h HUnit)) => HEqIx (LVar h) where
  heqIx (LVar _ x) (LVar _ y) =
    case heqIx x y of
      Just Refl -> Just Refl
      Nothing   -> Nothing

instance (HOrd (h HUnit)) => HOrd (LVar h) where
  hcompare (LVar n x) (LVar m y) = compare n m <> hcompare x y

instance (HOrdIx (h HUnit)) => HOrdIx (LVar h) where
  hcompareIx (LVar _ x) (LVar _ y) = hcompareIx x y

instance HShow (LVar f) where
  hshowsPrec n (LVar m _) = \xs -> showParen (n == 11) (\ys -> "LVar " ++ show m ++ ys) xs

-- suc :: LVar h ix -> LVar h ix
-- suc (LVar n x) = LVar (n + 1) x
--
-- suc' :: (HFunctor h) => LVar h ix -> h f ix' -> LVar h ix'
-- suc' (LVar n _) y = LVar (n + 1) $ hfmap (const $ K ()) y

mkLVar :: (HFunctor h) => Integer -> h f ix -> LVar h ix
mkLVar n x = LVar n $ hfmap (const $ K ()) x

type ClosedTerm h = HFix h

type Term h = HFree h (LVar h)

newtype Subst h = Subst (HMap (LVar h) (Term h))

lookup :: (HOrdIx (h HUnit)) => LVar h ix -> Subst h -> Maybe (Term h ix)
lookup k (Subst s) = HM.lookup k s

lookupVar :: Integer -> Subst h -> Maybe (Some (Term h))
lookupVar n (Subst s) = HM.lookupWith (\(LVar m _) -> compare n m) s

extend :: (HOrdIx (h HUnit)) => LVar h ix -> Term h ix -> Subst h -> Subst h
extend k v (Subst s) = Subst $ HM.insert k v s

domain :: Subst h -> [Some (LVar h)]
domain (Subst s) = HM.keys s

empty :: Subst t
empty = Subst HM.empty

