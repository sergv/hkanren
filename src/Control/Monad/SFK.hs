----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.SFK
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
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Control.Monad.SFK
  ( SFK )
where

import Control.Applicative
import Control.Monad
import Control.Monad.AbstractLogic
import Data.Functor.Identity
import Data.Pointed

newtype SFK a = SFK { runSFK :: forall r. (a -> r -> r) -> r -> r }

instance (Show a) => Show (SFK a) where
  show (SFK f) = f (\x _ -> "SFK <success>, x = " ++ show x) "SFK <fail>"

concatCont :: SFK a -> SFK a -> SFK a
concatCont (SFK f) (SFK g) =
  SFK (\sk fk -> f sk (g sk fk))

appCont :: SFK (a -> b) -> SFK a -> SFK b
appCont (SFK f) (SFK g) =
  SFK (\sk fk -> f (\h fk' -> g (\x fk'' -> sk (h x) fk'') fk') fk)

bindCont :: SFK a -> (a -> SFK b) -> SFK b
bindCont (SFK f) g =
  SFK (\sk fk -> f (\x fk' -> runSFK (g x) sk fk') fk)

splitCont :: forall a. SFK a -> SFK (Maybe (a, SFK a))
splitCont (SFK f) = SFK go
  where
    go :: forall r. (Maybe (a, SFK a) -> r -> r) -> r -> r
    go sk fk = sk (f g h) fk
      -- case f g h of
      --   Nothing    -> fk
      --   x@(Just _) -> sk x fk
      where
        g :: a -> Maybe (a, SFK a) -> Maybe (a, SFK a)
        g x fk' = Just (x, maybe mzero (\(x', m) -> return x' `mplus` m) fk')
        h :: Maybe (a, SFK a)
        h = Nothing

sfk2list :: SFK a -> [a]
sfk2list (SFK f) = f (:) []

instance Functor SFK where
  fmap f (SFK g) = SFK $ \sk fk -> g (\x fk' -> sk (f x) fk') fk
  -- fmap f (SFK g) = SFK $ \sk -> g (\x -> sk (f x))

instance Pointed SFK where
  point x = SFK (\sk fk -> sk x fk)

instance Applicative SFK where
  pure = point
  (<*>) = appCont

instance Monad SFK where
  (>>=) = bindCont

instance Alternative SFK where
  empty = SFK (\_ fk -> fk)
  (<|>) = concatCont

instance MonadPlus SFK

instance AbstractLogic SFK Identity where
  (>>-) x f = do
    s <- splitCont x
    case s of
      Nothing      -> mzero
      Just (a, x') -> f a `interleave` (x' >>- f)
  interleave x y = do
    s <- splitCont x
    case s of
      Nothing      -> y
      Just (a, x') -> return a `mplus` interleave y x'
  failure = empty
  observeAll = pure . sfk2list

