----------------------------------------------------------------------------
-- |
-- Module      :  Control.Nondet
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE MultiParamTypeClasses #-}

module Control.Nondet where

import Control.Applicative

class Nondet c where
  failure :: c a
  choice  :: c a -> c a -> c a

class (Applicative m, Nondet c) => Observable c m where
  observeNondetAll :: c a -> m [a]

observeNondetMany :: (Nondet c, Observable c n) => Int -> c a -> n [a]
observeNondetMany n = fmap (take n) . observeNondetAll
