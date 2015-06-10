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

{-# LANGUAGE DoAndIfThenElse            #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverlappingInstances       #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE UndecidableInstances       #-}

module Control.Monad.ContNondet
  ( Nondet(..)
  , Observable(..)
  , ContNondet
  , unwrapContNondet
  , ContNondetT(..)
  , unwrapContNondetT
  , RandomSourceState
  , runRandomSourceState
  , Depth(..)
  , DepthConfig
  , mkDepthConfig
  )
where

import Control.Applicative
import Control.Arrow (second)
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
import Data.Random.Source (MonadRandom(..))
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

-- requires UndecidableInstances
instance (MonadState s m) => MonadState s (ContNondetT c m) where
  get = lift get
  put = lift . put

instance (Nondet c, Applicative m) => Alternative (ContNondetT c m) where
  empty = ContNondetT $ \_ -> pure failure
  ContNondetT f <|> ContNondetT g = ContNondetT $ \k -> choice <$> f k <*> g k

instance (Nondet c, Applicative m) => MonadPlus (ContNondetT c m) where
  mzero = empty
  mplus = (<|>)

------------------------------------------------------------------------
-- Vanilla abstract logic instance. Has dummy probabilisticChoice that's
-- isomorphic to foldr interleave failure.

instance (Pointed c, Nondet c, Observable c Identity) => AbstractLogic (ContNondetT c Identity) Identity where
  (>>-)         = (>>=)
  interleave    = foldr (<|>) empty
  failure       = empty
  observeAll    = observeNondetAll <=< unwrapContNondetT
  observeMany n = observeNondetMany n <=< unwrapContNondetT

-- instance (Pointed c, Nondet c, Observable c m) => AbstractLogic (ContNondetT c m) m where
--   (>>-)         = (>>=)
--   interleave    = (<|>)
--   failure       = empty
--   observeAll    = observeNondetAll <=< unwrapContNondetT
--   observeMany n = observeNondetMany n <=< unwrapContNondetT

------------------------------------------------------------------------
-- Abstract logic instance with real probabilisticChoice that drops some branches.

instance (Pointed c, Nondet c, Observable c (State PureMT)) => AbstractLogic (ContNondetT c (State PureMT)) (State PureMT) where
  (>>-)               = (>>=)
  interleave          = foldr (<|>) empty
  failure             = empty
  probabilisticChoice = weighted
  observeAll          = observeNondetAll <=< unwrapContNondetT
  observeMany n       = observeNondetMany n <=< unwrapContNondetT

weighted
  :: forall c m n a. (AbstractLogic (ContNondetT c m) n, MonadRandom m)
  => [(Int, ContNondetT c m a)]
  -> ContNondetT c m a
weighted [] = AL.failure
weighted cs = do
  cs' <- map snd <$> filterM (f . fst) cs
  -- trace ("weighted: continuing with " ++ show (length cs') ++ "/" ++ show (length cs)) $
  AL.interleave cs'
  where
    totalWeight = sum $ map fst cs
    totalWeight' = totalWeight - 1
    f :: Int -> ContNondetT c m Bool
    f w = do
      w' <- lift $ sample (uniform 0 totalWeight')
      return $ w' < w

------------------------------------------------------------------------
-- RandomSourceState to define instance that drops branches in
-- probabilisticChoice only after certain depth is reached.

newtype RandomSourceState s a = RandomSourceState (StateT PureMT (State s) a)
  deriving (Functor, Applicative, Monad)

runRandomSourceState :: RandomSourceState s a -> PureMT -> s -> a
runRandomSourceState (RandomSourceState x) mt s =
  evalState (evalStateT x mt) s

instance MonadRandom (RandomSourceState s) where
  getRandomWord8        = RandomSourceState getRandomWord8
  getRandomWord16       = RandomSourceState getRandomWord16
  getRandomWord32       = RandomSourceState getRandomWord32
  getRandomWord64       = RandomSourceState getRandomWord64
  getRandomDouble       = RandomSourceState getRandomDouble
  getRandomNByteInteger = RandomSourceState . getRandomNByteInteger

newtype Depth = Depth { getDepth :: Int }
  deriving (Show, Eq, Ord)

incrementDepth :: Depth -> Depth
incrementDepth = Depth . inc . getDepth
  where
    inc x = x' `seq` x'
      where
        x' = x + 1

instance MonadState s (RandomSourceState s) where
  get = RandomSourceState $ lift get
  put = RandomSourceState . lift . put

data DepthConfig = DepthConfig
  { dcCurrDepth   :: Depth
  -- | Depth after which probabilisticChoice will start dropping branches.
  , dcTargetDepth :: Depth
  }
  deriving (Show, Eq, Ord)

mkDepthConfig :: Depth -> DepthConfig
mkDepthConfig target = DepthConfig
  { dcCurrDepth   = Depth 0
  , dcTargetDepth = target
  }

instance (Pointed c, Nondet c, Observable c (RandomSourceState DepthConfig)) =>
         AbstractLogic (ContNondetT c (RandomSourceState DepthConfig)) (RandomSourceState DepthConfig) where
  (>>-)                  = (>>=)
  interleave []          = empty
  interleave xs          = do
    modify (\c -> c { dcCurrDepth = incrementDepth $ dcCurrDepth c })
    depth <- get
    foldr (<|>) empty $ map (put depth >>) xs
  failure                = empty
  probabilisticChoice [] = empty
  probabilisticChoice cs = do
    DepthConfig curr target <- get
    modify (\c -> c { dcCurrDepth = incrementDepth $ dcCurrDepth c })
    depth <- get
    if curr >= target
    then weighted $ map (second (put depth >>)) cs
    else AL.interleave $ map snd cs
  observeAll             = observeNondetAll <=< unwrapContNondetT
  observeMany n          = observeNondetMany n <=< unwrapContNondetT

------------------------------------------------------------------------
-- ContNondet alias

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
