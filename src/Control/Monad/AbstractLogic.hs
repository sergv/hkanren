----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.AbstractLogic
-- Copyright   :  (m) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Control.Monad.AbstractLogic (AbstractLogic(..), chooseWeightedBranch) where

-- import Control.Monad.State
import Data.Pointed

class (Pointed m, Functor n) => AbstractLogic m n | m -> n where
  -- conjunction
  (>>-)               :: m a -> (a -> m b) -> m b
  -- disjunction
  interleave          :: m a -> m a -> m a
  failure             :: m a
  probabilisticChoice :: [(Int, m a)] -> m a
  probabilisticChoice = foldr interleave failure . map snd
  observeAll          :: m a -> n [a]
  observeMany         :: Int -> m a -> n [a]
  observeMany n = fmap (take n) . observeAll

-- instance (AbstractLogic n, Monad n) => AbstractLogic (StateT s n) where
--   (>>-) x f = x >>= \x' -> x' >>- f
--   interleave x y = do
--     x' <- x
--     y' <- y
--     lift $ interleave x' y'
--   failure = lift failure

chooseWeightedBranch :: Int -> Int -> a -> [(Int, a)] -> a
chooseWeightedBranch _     _            defCase [] = defCase
chooseWeightedBranch accum targetWeight defCase ((w, x) : xs)
  | targetWeight < accum = x
  | otherwise            = chooseWeightedBranch accum' targetWeight defCase xs
  where
    accum' = accum + w

