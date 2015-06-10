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

module Language.HKanren.IntLVar
  (LVar)
where

import Control.DeepSeq
import Data.HOrdering
import Data.HUtils
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.Type.Equality
import qualified Text.PrettyPrint.Leijen.Text as PP

import qualified Language.HKanren.LVar as L
import Language.HKanren.Type

import Unsafe.Coerce

type LTerm h = HFree h (LVar h)

newtype LVar (f :: (* -> *) -> (* -> *)) ix = LVar Int

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
    {-# SCC hcompareIx_int_lvar #-}
    case compare n m of
      LT -> HLT
      EQ -> unsafeCoerce HEQ
      GT -> HGT
  hcompareHet (LVar n) (LVar m) = {-# SCC hcompareHet_int_lvar #-} compare n m

instance HShow (LVar f) where
  hshowsPrec n (LVar m) = \xs -> showParen (n == 11) (\ys -> "LVar " ++ show m ++ ys) xs

instance HPretty (LVar f) where
  hpretty (LVar m) = PP.angles $ PP.int m

instance HNFData (LVar f) where
  hrnf (LVar m) = rnf m


instance (HOrdHet (Type (h (LTerm h)))) => L.LVar (LVar h) where
  type LFunctor (LVar h) = h
  type LDomain (LVar h)  = Int
  newtype LMap (LVar h)  = IntLMap { getIntLMap :: IntMap (Some (LTerm h)) }
  mkLVar = LVar . fromIntegral
  getDomain (LVar x) = x

  empty  = IntLMap IM.empty
  size   = fromIntegral . IM.size . getIntLMap
  insert (LVar k) v = IntLMap . IM.insert k (Some v) . getIntLMap
  lookup (LVar k) m =
    case IM.lookup k $ getIntLMap m of
      Nothing       -> Nothing
      Just (Some x) -> Just $ unsafeCoerce x
  domain = IM.keys . getIntLMap
  keys   = map (Some . LVar) . IM.keys . getIntLMap
  toList = map (\(k, Some v) -> (Some $ LVar k :*: v)) . IM.toList . getIntLMap

