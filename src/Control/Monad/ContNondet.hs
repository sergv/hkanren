----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.ContNondet
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances  #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Control.Monad.ContNondet
  ( Nondet(..)
  , Observable(..)
  , ContNondet
  , unwrapContNondet
  , ContNondetT(..)
  , unwrapContNondetT
  )
where

import Control.Applicative
import Control.Monad
import Control.Monad.AbstractLogic (AbstractLogic)
import qualified Control.Monad.AbstractLogic as AL
import Control.Monad.Reader
import Control.Monad.State
import Control.Nondet
import Data.Functor.Identity
import Data.Pointed
import Data.Random.Distribution.Uniform (uniform)
import Data.Random.Sample (sample)
import Data.Random.Source (MonadRandom)
import Data.Random.Source.PureMT (PureMT)

-- c - type of nondeterministic computations
newtype ContNondetT c m a = ContNondetT { runContNondetT :: forall b. (a -> m (c b)) -> m (c b) }

unwrapContNondetT :: (Pointed c, Applicative m) => ContNondetT c m a -> m (c a)
unwrapContNondetT x = runContNondetT x (pure . point)

instance Functor (ContNondetT c m) where
  fmap f (ContNondetT g) = ContNondetT $ \k -> g (k . f)

instance Pointed (ContNondetT c m) where
  point x = ContNondetT ($ x)

instance Applicative (ContNondetT c m) where
  pure = point
  (<*>) (ContNondetT f) (ContNondetT g) = ContNondetT $ \k -> f (\h -> g (\x -> k (h x)))

instance Monad (ContNondetT c m) where
  (>>=) (ContNondetT f) g = ContNondetT $ \k -> f (\x -> runContNondetT (g x) k)

instance MonadTrans (ContNondetT c) where
  lift x = ContNondetT $ \k -> x >>= k

instance (Nondet c, Applicative m) => Alternative (ContNondetT c m) where
  empty = ContNondetT $ \_ -> pure failure
  ContNondetT f <|> ContNondetT g = ContNondetT $ \k -> choice <$> f k <*> g k

instance (Nondet c, Applicative m) => MonadPlus (ContNondetT c m) where
  mzero = empty
  mplus = (<|>)

instance (Pointed c, Nondet c, Observable c Identity) => AbstractLogic (ContNondetT c Identity) Identity where
  (>>-)         = (>>=)
  interleave    = (<|>)
  failure       = empty
  observeAll    = fmap (runIdentity . observeNondetAll) . unwrapContNondetT
  observeMany n = fmap (runIdentity . observeNondetMany n) . unwrapContNondetT

-- instance (Pointed c, Nondet c, Observable c m) => AbstractLogic (ContNondetT c m) m where
--   (>>-)         = (>>=)
--   interleave    = (<|>)
--   failure       = empty
--   observeAll    = observeNondetAll <=< unwrapContNondetT
--   observeMany n = observeNondetMany n <=< unwrapContNondetT

instance (Pointed c, Nondet c, Observable c (State PureMT)) => AbstractLogic (ContNondetT c (State PureMT)) (State PureMT) where
  (>>-)               = (>>=)
  interleave          = (<|>)
  failure             = empty
  probabilisticChoice = weighted
  observeAll          = observeNondetAll <=< unwrapContNondetT
  observeMany n       = observeNondetMany n <=< unwrapContNondetT

weighted :: (AbstractLogic (ContNondetT c m) n, MonadRandom m)
         => [(Int, ContNondetT c m a)]
         -> ContNondetT c m a
weighted []            = AL.failure
weighted cs@((_, c):_) = do
  x <- lift $ sample (uniform 0 (totalWeight - 1))
  AL.chooseWeightedBranch 0 x c cs
  where
    totalWeight = sum $ map fst cs


type ContNondet c = ContNondetT c Identity

unwrapContNondet :: (Pointed c) => ContNondet c a -> c a
unwrapContNondet = runIdentity . unwrapContNondetT

-- -- Type of continuations parameterised by some nondeterminism.
-- -- c - type of nondeterministic computations
-- newtype ContNondet c a = ContNondet { runContNondet :: forall b. (a -> c b) -> c b }
--
-- unwrapContNondet :: (Pointed c) => ContNondet c a -> c a
-- unwrapContNondet x = runContNondet x point
--
-- instance Functor (ContNondet c) where
--   fmap f (ContNondet g) = ContNondet $ \k -> g (k . f)
--
-- instance Pointed (ContNondet c) where
--   point x = ContNondet ($ x)
--
-- instance Applicative (ContNondet c) where
--   pure = point
--   (<*>) (ContNondet f) (ContNondet g) = ContNondet $ \k -> f (\h -> g (\x -> k (h x)))
--
-- instance Monad (ContNondet c) where
--   (>>=) (ContNondet f) g = ContNondet $ \k -> f (\x -> runContNondet (g x) k)
--
--
-- instance (Nondet c) => Alternative (ContNondet c) where
--   empty = ContNondet $ \_ -> failure
--   ContNondet f <|> ContNondet g = ContNondet $ \k -> f k `choice` g k
--
-- instance (Nondet c) => MonadPlus (ContNondet c) where
--   mzero = empty
--   mplus = (<|>)
--
--
-- instance (Nondet c) => AbstractLogic (ContNondet c) Identity where
--   (>>-)         = (>>=)
--   interleave    = (<|>)
--   failure       = empty
--   observeAll    = pure . observeNondetAll . unwrapContNondet
--   observeMany n = pure . observeNondetMany n . unwrapContNondet
