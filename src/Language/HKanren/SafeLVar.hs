----------------------------------------------------------------------------
-- |
-- Module      :  Language.HKanren.LVar
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

module Language.HKanren.SafeLVar
  (LVar)
where

import Control.DeepSeq
import Data.HOrdering
import Data.HUtils
import Data.HMap (HMap)
import qualified Data.HMap as HM
import qualified Text.PrettyPrint.Leijen.Text as PP

import qualified Language.HKanren.LVar as L
import Language.HKanren.Type

type LTerm h = HFree h (LVar h)

-- | Logic variable.
data LVar (f :: (* -> *) -> (* -> *)) ix where
  LVar :: !Integer -> !(Type (f (LTerm f)) ix) -> LVar f ix

instance HEq (LVar h) where
  {-# INLINABLE heq #-}
  heq (LVar n _) (LVar m _) = n == m

instance (HEqHet (Type (h (LTerm h)))) => HEqHet (LVar h) where
  {-# INLINABLE heqIx #-}
  heqIx (LVar _ x) (LVar _ y) = heqIx x y
  (==*) (LVar n _) (LVar m _) = n == m

instance HOrd (LVar h) where
  {-# INLINABLE hcompare #-}
  hcompare (LVar n _) (LVar m _) = compare n m

instance (HOrdHet (Type (h (LTerm h)))) => HOrdHet (LVar h) where
  {-# INLINABLE hcompareIx #-}
  hcompareIx (LVar _ x) (LVar _ y) = {-# SCC hcompareIx_safe_lvar #-} hcompareIx x y
  hcompareHet (LVar n _) (LVar m _) = {-# SCC hcompareHet_safe_lvar #-} compare n m

instance HShow (LVar f) where
  hshowsPrec n (LVar m _) = \xs -> showParen (n == 11) (\ys -> "LVar " ++ show m ++ ys) xs

instance HPretty (LVar f) where
  hpretty (LVar m _) = PP.angles $ PP.integer m

instance (HNFData (Type (f (LTerm f)))) => HNFData (LVar f) where
  hrnf (LVar m t) = rnf m `seq` hrnf t

mkLVar :: (TypeI (h (LTerm h)) ix) => Integer -> LVar h ix
mkLVar n = LVar n singType

instance (HOrdHet (Type (h (LTerm h)))) => L.LVar (LVar h) where
  type LFunctor (LVar h) = h
  type LDomain (LVar h)  = Integer
  newtype LMap (LVar h)  = SafeLMap { getSafeLMap :: HMap (LVar h) (LTerm h) }
  mkLVar = mkLVar
  getDomain (LVar x _) = x

  empty  = SafeLMap HM.empty
  size   = fromIntegral . HM.size . getSafeLMap
  insert k v = SafeLMap . HM.insert k v . getSafeLMap
  lookup k = HM.lookup k . getSafeLMap
  domain = HM.domain . getSafeLMap
  keys   = HM.keys . getSafeLMap
  toList = HM.toList . getSafeLMap

