----------------------------------------------------------------------------
-- |
-- Module      :  Data.Levels
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Data.Levels (Levels, runLevels) where

import Control.Nondet
import Data.Pointed

newtype Levels c a = Levels { getLevels :: [c a] }

runLevels :: (Nondet c) => Levels c a -> c a
runLevels = foldr choice failure . getLevels

instance (Pointed c) => Pointed (Levels c) where
  point = Levels . (:[]) . point

instance (Nondet c) => Nondet (Levels c) where
  failure = Levels []
  choice (Levels xs) (Levels ys) = Levels $ failure : merge xs ys

instance (Nondet c, Observable c m) => Observable (Levels c) m where
  observeNondetAll = observeNondetAll . runLevels

merge :: (Nondet c) => [c a] -> [c a] -> [c a]
merge []     ys     = ys
merge xs     []     = xs
merge (x:xs) (y:ys) = choice x y : merge xs ys

-- levelSearch :: ContNondet (Levels DiffList) a -> [a]
-- levelSearch = toList . runLevels . unwrapContNondet

