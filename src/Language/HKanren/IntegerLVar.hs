----------------------------------------------------------------------------
-- |
-- Module      :  Language.HKanren.IntegerLVar
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
-- Unsafe but fast Integer-based LVars.
----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.HKanren.IntegerLVar
  (LVar)
where

import Control.DeepSeq
import Data.HOrdering
import Data.HUtils
import Data.Map (Map)
import qualified Data.Map as M
import Data.Type.Equality
import qualified Text.PrettyPrint.Leijen.Text as PP

import qualified Language.HKanren.LVar as L
import Language.HKanren.Type

import Unsafe.Coerce

type LTerm h = HFree h (LVar h)

newtype LVar (f :: (* -> *) -> (* -> *)) ix = LVar Integer

instance HEq (LVar h) where
  {-# INLINABLE heq #-}
  heq (LVar n) (LVar m) = n == m

instance (HEqHet (Type (h (LTerm h)))) => HEqHet (LVar h) where
  {-# INLINABLE heqIx #-}
  heqIx (LVar n) (LVar m) =
    if n == m
       then unsafeCoerce $ Just Refl
       else Nothing
  (==*) (LVar n) (LVar m) = n == m

instance HOrd (LVar h) where
  {-# INLINABLE hcompare #-}
  hcompare (LVar n) (LVar m) = compare n m

instance (HOrdHet (Type (h (LTerm h)))) => HOrdHet (LVar h) where
  {-# INLINABLE hcompareIx #-}
  hcompareIx (LVar n) (LVar m) =
    {-# SCC hcompareIx_integer_lvar #-}
    case compare n m of
      LT -> HLT
      EQ -> unsafeCoerce HEQ
      GT -> HGT
  hcompareHet (LVar n) (LVar m) = {-# SCC hcompareHet_integer_lvar #-} compare n m

instance HShow (LVar f) where
  hshowsPrec n (LVar m) = \xs -> showParen (n == 11) (\ys -> "LVar " ++ show m ++ ys) xs

instance HPretty (LVar f) where
  hpretty (LVar m) = PP.angles $ PP.integer m

instance HNFData (LVar f) where
  hrnf (LVar m) = rnf m


instance (HOrdHet (Type (h (LTerm h)))) => L.LVar (LVar h) where
  type LFunctor (LVar h) = h
  type LDomain (LVar h)  = Integer
  newtype LMap (LVar h)  = IntegerLMap { getIntegerLMap :: Map Integer (Some (LTerm h)) }
  mkLVar = LVar
  getDomain (LVar x) = x

  empty  = IntegerLMap M.empty
  size   = fromIntegral . M.size . getIntegerLMap
  insert (LVar k) v = IntegerLMap . M.insert k (Some v) . getIntegerLMap
  lookup (LVar k) m =
    case M.lookup k $ getIntegerLMap m of
      Nothing       -> Nothing
      Just (Some x) -> Just $ unsafeCoerce x
  domain = M.keys . getIntegerLMap
  keys   = map (Some . LVar) . M.keys . getIntegerLMap
  toList = map (\(k, Some v) -> (Some $ LVar k :*: v)) . M.toList . getIntegerLMap

