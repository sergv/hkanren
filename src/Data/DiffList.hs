----------------------------------------------------------------------------
-- |
-- Module      :  Data.DiffList
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Data.DiffList (DiffList, toList) where

import Control.Nondet
import Data.Pointed

newtype DiffList a = DiffList ([a] -> [a])

toList :: DiffList a -> [a]
toList (DiffList f) = f []

instance Pointed DiffList where
  point x = DiffList (x:)

instance Nondet DiffList where
  failure = DiffList id -- (const [])
  choice (DiffList f) (DiffList g) = DiffList (f . g)

instance (Applicative m) => Observable DiffList m where
  observeNondetAll = pure . toList
