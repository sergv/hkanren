----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.InterleavingLogic
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE InstanceSigs        #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Control.Monad.InterleavingLogic
  ( Logic
  , logic
  , observe
  , observeAll
  , observeMany
  , runLogic
  )
where

import Control.Applicative
import Control.Monad
import Control.Monad.Logic.Class

import qualified Data.Foldable as F
import qualified Data.Traversable as T

-- msplit' ssk fk m = lift $ unLogicT m (\x ma -> ssk x (lift ma)) fk


-------------------------------------------------------------------------
-- | The basic Logic monad, for performing backtracking computations
-- returning values of type 'a'
newtype Logic a = Logic { unLogic :: forall r. (a -> r -> r) -> r -> r }

-------------------------------------------------------------------------
-- | A smart constructor for Logic computations.
logic :: (forall r. (a -> r -> r) -> r -> r) -> Logic a
logic = Logic

-------------------------------------------------------------------------
-- | Extracts the first result from a Logic computation.
observe :: Logic a -> a
observe l = unLogic l const (error "No answer.")

-------------------------------------------------------------------------
-- | Extracts all results from a Logic computation.
observeAll :: Logic a -> [a]
observeAll l = unLogic l (:) []

-------------------------------------------------------------------------
-- | Extracts up to a given number of results from a Logic computation.
observeMany :: forall a. Int -> Logic a -> [a]
observeMany n m
    | n <= 0    = []
    | n == 1    = unLogic m (\a _ -> [a]) []
    | otherwise = unLogic (msplit m) sk []
 where
 sk :: Maybe (a, Logic a) -> [a] -> [a]
 sk Nothing        _ = []
 sk (Just (a, m')) _ = n' `seq` (a : observeMany n' m')
   where
     n' = n - 1


-------------------------------------------------------------------------
-- | Runs a Logic computation with the specified initial success and
-- failure continuations.
runLogic :: Logic a -> (a -> r -> r) -> r -> r
runLogic = unLogic

instance Functor Logic where
  {-# INLINABLE fmap #-}
  fmap f lt = Logic $ \sk fk -> unLogic lt (sk . f) fk

instance Applicative Logic where
  {-# INLINABLE pure #-}
  pure a = Logic $ \sk fk -> sk a fk
  {-# INLINABLE (<*>) #-}
  f <*> a = Logic $ \sk fk -> unLogic f (\g fk' -> unLogic a (sk . g) fk') fk

instance Alternative Logic where
  {-# INLINABLE empty #-}
  empty = Logic $ \_ fk -> fk
  {-# INLINABLE (<|>) #-}
  f1 <|> f2 = Logic $ \sk fk -> unLogic f1 sk (unLogic f2 sk fk)

instance Monad Logic where
  {-# INLINABLE return #-}
  return a = Logic $ \sk fk -> sk a fk
  {-# INLINABLE (>>=) #-}
  m >>= f = Logic $ \sk fk -> unLogic m (\a fk' -> unLogic (f a) sk fk') fk
  fail _ = Logic $ \_ fk -> fk

instance MonadPlus Logic where
  {-# INLINABLE mzero #-}
  mzero = Logic $ \_ fk -> fk
  {-# INLINABLE mplus #-}
  m1 `mplus` m2 = Logic $ \sk fk -> unLogic m1 sk (unLogic m2 sk fk)

instance MonadLogic Logic where
  {-# INLINABLE msplit #-}
  msplit :: forall a. Logic a -> Logic (Maybe (a, Logic a))
  msplit m = unLogic m ssk (return Nothing)
    where
      ssk :: a -> Logic (Maybe (a, Logic a)) -> Logic (Maybe (a, Logic a))
      ssk a fk = return $ Just (a, (fk >>= reflect))

  -- msplit' :: forall a b. (a -> Logic a -> Logic b) -> Logic b -> Logic a -> Logic b
  -- msplit' f g m = unLogic m ssk g
  --   where
  --     ssk :: a -> Logic b -> Logic b
  --     ssk a fk = undefined

instance F.Foldable Logic where
  foldMap f m = unLogic m (mappend . f) mempty

instance T.Traversable Logic where
  traverse g l = unLogic l (\a ft -> cons <$> g a <*> ft) (pure mzero)
    where
      cons a l' = return a `mplus` l'
