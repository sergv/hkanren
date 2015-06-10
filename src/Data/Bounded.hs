----------------------------------------------------------------------------
-- |
-- Module      :  Data.Bounded
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
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Data.Bounded where

import Control.Applicative
import Control.Monad.AbstractLogic (AbstractLogic)
import qualified Control.Monad.AbstractLogic as AL
import Control.Monad.ContNondet
import Control.Monad.Reader
import Data.Pointed

import Prelude hiding (Bounded)

newtype Bounded c a = Bounded { getBounded :: Int -> c a }

instance (Nondet c) => Nondet (Bounded c) where
  failure = Bounded $ \_ -> failure
  choice (Bounded f) (Bounded g) = Bounded h
    where
      h 0 = failure
      h d = d' `seq` choice (f d') (g d')
        where
          d' = pred d

instance (Nondet c, Observable c m, MonadReader Int m) => Observable (Bounded c) m where
  observeNondetAll x = do
    n <- ask
    observeNondetAll $ getBounded x n

instance (Pointed c, Nondet c, Observable c m, MonadReader Int m) => AbstractLogic (ContNondetT (Bounded c) m) m where
  (>>-)        = (>>=)
  interleave   = foldr (<|>) empty
  failure      = empty
  observeAll x = do
    step <- ask
    observeNondetAll =<< depthFirst step x
  -- observeMany n = observeNondetMany n <=< unwrapContNondetT

levelIter :: forall c m a. (Pointed c, Nondet c, Monad m) => Int -> ContNondetT (Bounded c) m a -> m [c a]
levelIter step x = forM [0, step ..] $ \d -> (`getBounded` d) <$> runContNondetT x pointB
  where
    pointB :: a -> m (Bounded c a)
    pointB x = return $ Bounded $ \d -> if d < step then point x else failure

depthFirst :: (Pointed c, Nondet c, Monad m) => Int -> ContNondetT (Bounded c) m a -> m (c a)
depthFirst step = return . foldr choice failure <=< levelIter step
