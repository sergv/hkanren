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
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Data.HMap
  ( HMap
  , empty
  , insert
  , lookup
  , lookupWith
  , keys
  , toList
  )
where

import Data.HOrdering
import Data.HUtils
import Prelude hiding (lookup)

data Color = Red | Black
  deriving (Show, Eq, Ord)

data HMap (k :: * -> *) (v :: * -> *) where
  HNil  :: HMap k v -- considered to be black
  HNode :: !Color -> !(k ix) -> !(v ix) -> !(HMap k v) -> !(HMap k v) -> HMap k v

instance (HShow k, HShow v) => Show (HMap k v) where
  showsPrec _ HNil = showString "HNil"
  showsPrec n (HNode c k v left right) =
    showParen (n == 11) $
    showString "HNode" . showString " " .
    showsPrec 11 c . showString " " .
    hshowsPrec 11 k . showString " " .
    hshowsPrec 11 v . showString " " .
    showsPrec 11 left . showString " " .
    showsPrec 11 right

empty :: HMap k v
empty = HNil

-- {-# INLINABLE insert #-}
insert :: forall k ix v. (HOrd k, HOrdHet k) => k ix -> v ix -> HMap k v -> HMap k v
insert k v node =
  mkBlack $ go k node
  where
    go :: k ix -> HMap k v -> HMap k v
    go k HNil                       = HNode Red k v HNil HNil
    go k (HNode c k' v' left right) =
      case hcompareHet k k' of
        LT -> balance c k' v' left' right
        EQ -> HNode c k v left right -- tree is already balanced, just replace the value
        GT -> balance c k' v' left right'
      where
        left'  = insert k v left
        right' = insert k v right

    mkBlack :: HMap k v -> HMap k v
    mkBlack HNil                     = HNil
    mkBlack (HNode _ k v left right) = HNode Black k v left right

    balance :: forall ix. Color -> k ix -> v ix -> HMap k v -> HMap k v -> HMap k v
    balance Black k v (HNode Red k' v' (HNode Red k'' v'' l'' r'') r') r =
      HNode Red k' v' (HNode Black k'' v'' l'' r'') (HNode Black k v r' r)
    balance Black k v (HNode Red k' v' l' (HNode Red k'' v'' l'' r'')) r =
      HNode Red k'' v'' (HNode Black k' v' l' l'') (HNode Black k v r'' r)

    balance Black k v l (HNode Red k' v' (HNode Red k'' v'' l'' r'') r') =
      HNode Red k'' v'' (HNode Black k v l l'') (HNode Black k' v' r'' r')
    balance Black k v l (HNode Red k' v' l' (HNode Red k'' v'' l'' r'')) =
      HNode Red k' v' (HNode Black k v l l') (HNode Black k'' v'' l'' r'')

    balance c k v l r = HNode c k v l r

lookupWith :: (forall ix. k ix -> Ordering) -> HMap k v -> Maybe (Some v)
lookupWith _ HNil = Nothing
lookupWith p (HNode _ k v left right) =
  case p k of
    LT -> lookupWith p left
    EQ -> Just $ Some v
    GT -> lookupWith p right

-- {-# INLINABLE lookup #-}
lookup :: (HOrd k, HOrdHet k) => k ix -> HMap k v -> Maybe (v ix)
lookup _ HNil = Nothing
lookup k (HNode _ k' v left right) =
  case hcompareHet k k' of
    LT -> lookup k left
    EQ ->
      case hcompareIx k k' of
        HLT -> lookup k left
        HEQ -> Just v
        HGT -> lookup k right
    GT -> lookup k right
  -- case hcompareIx k k' of
  --   HLT -> lookup k left
  --   HEQ ->
  --     case hcompare k k' of
  --       LT -> lookup k left
  --       EQ -> Just v
  --       GT -> lookup k right
  --   HGT -> lookup k right

keys :: forall k v. HMap k v -> [Some k]
keys m = go m []
  where
    go :: HMap k v -> [Some k] -> [Some k]
    go HNil xs                     = xs
    go (HNode _ k _ left right) xs = go left $ Some k : go right xs

toList :: forall k v. HMap k v -> [Some (k :*: v)]
toList m = go m []
  where
    go :: HMap k v -> [Some (k :*: v)] -> [Some (k :*: v)]
    go HNil xs                     = xs
    go (HNode _ k v left right) xs = go left $ Some (k :*: v) : go right xs
