----------------------------------------------------------------------------
-- |
-- Module      :  Data.HMap
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.HMap
  ( HMap
  , empty
  , insert
  , lookup
  , lookupWith
  , keys
  )
where

import Data.HOrdering
import Data.HUtils
import Data.Type.Equality
import Prelude hiding (lookup)

data HMap (k :: * -> *) (v :: * -> *) where
  HNil  :: HMap k v
  HNode :: k ix -> v ix -> HMap k v -> HMap k v -> HMap k v

empty :: HMap k v
empty = HNil

insert :: (HOrdHet k) => k ix -> v ix -> HMap k v -> HMap k v
insert k v HNil = HNode k v HNil HNil
insert k v (HNode k' v' left right) =
  case hcompareHet k k' of
    LT -> HNode k' v' left' right
    EQ -> HNode k v left right
    GT -> HNode k' v' left right'
  where
    left' = insert k v left
    right' = insert k v right

lookupWith :: (forall ix. k ix -> Ordering) -> HMap k v -> Maybe (Some v)
lookupWith _ HNil = Nothing
lookupWith p (HNode k v left right) =
  case p k of
    LT -> lookupWith p left
    EQ -> Just $ Some v
    GT -> lookupWith p right

lookup :: (HOrdHet k) => k ix -> HMap k v -> Maybe (v ix)
lookup _ HNil = Nothing
lookup k (HNode k' v left right) =
  -- case hcompareHet k k' of
  --   LT -> lookup k left
  --   EQ ->
  --   GT -> lookup k right
  --
  case hcompareIx k k' of
    HLT      -> lookup k left
    HEQ Refl ->
      case hcompare k k' of
        LT -> lookup k left
        EQ -> Just v
        GT -> lookup k right
    HGT      -> lookup k right

keys :: forall k v. HMap k v -> [Some k]
keys m = go m []
  where
    go :: HMap k v -> [Some k] -> [Some k]
    go HNil xs = xs
    go (HNode k _ left right) xs = go left $ Some k : go right xs
