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

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Data.HMap
  ( HMap
  , empty
  , size
  , insert
  , lookup
  , domain
  , keys
  , toList
  )
where

import Language.HKanren.LVar (LVar)
import qualified Language.HKanren.LVar as L
import Data.HOrdering
import Data.HUtils
import Prelude hiding (lookup)


data Color = Red | Black
  deriving (Show, Eq, Ord)

data HMap (k :: * -> *) (v :: * -> *) where
  HNil  :: HMap k v -- considered to be black
  HNode :: !Color -> {-# UNPACK #-} !Int -> !(k ix) -> !(v ix) -> !(HMap k v) -> !(HMap k v) -> HMap k v

instance (HShow k, HShow v) => Show (HMap k v) where
  showsPrec _ HNil = showString "HNil"
  showsPrec n (HNode c s k v left right) =
    showParen (n == 11) $
    showString "HNode" . showString " " .
    showsPrec 11 c . showString " " .
    showsPrec 11 s . showString " " .
    hshowsPrec 11 k . showString " " .
    hshowsPrec 11 v . showString " " .
    showsPrec 11 left . showString " " .
    showsPrec 11 right

empty :: HMap k v
empty = HNil

size :: HMap k v -> Int
size HNil                = 0
size (HNode _ s _ _ _ _) = s

-- {-# INLINABLE insert #-}
insert :: forall k ix v. (HOrd k, HOrdHet k) => k ix -> v ix -> HMap k v -> HMap k v
insert k v node =
  mkBlack $ go k node
  where
    go :: k ix -> HMap k v -> HMap k v
    go k HNil                         = HNode Red 0 k v HNil HNil
    go k (HNode c s k' v' left right) =
      case hcompareHet k k' of
        LT -> balance c k' v' left' right
        EQ -> HNode c s k v left right -- tree is already balanced, just replace the value
        GT -> balance c k' v' left right'
      where
        left'  = insert k v left
        right' = insert k v right

    mkBlack :: HMap k v -> HMap k v
    mkBlack HNil                       = HNil
    mkBlack (HNode _ s k v left right) = HNode Black s k v left right

    balance :: forall ix. Color -> k ix -> v ix -> HMap k v -> HMap k v -> HMap k v
    balance Black k v (HNode Red _ k' v' (HNode Red _ k'' v'' l'' r'') r') r =
      mkHNode Red k' v' (mkHNode Black k'' v'' l'' r'') (mkHNode Black k v r' r)
    balance Black k v (HNode Red _ k' v' l' (HNode Red _ k'' v'' l'' r'')) r =
      mkHNode Red k'' v'' (mkHNode Black k' v' l' l'') (mkHNode Black k v r'' r)

    balance Black k v l (HNode Red _ k' v' (HNode Red _ k'' v'' l'' r'') r') =
      mkHNode Red k'' v'' (mkHNode Black k v l l'') (mkHNode Black k' v' r'' r')
    balance Black k v l (HNode Red _ k' v' l' (HNode Red _ k'' v'' l'' r'')) =
      mkHNode Red k' v' (mkHNode Black k v l l') (mkHNode Black k'' v'' l'' r'')

    balance c k v l r = mkHNode c k v l r

    mkHNode :: forall ix. Color -> k ix -> v ix -> HMap k v -> HMap k v -> HMap k v
    mkHNode c k v l r = HNode c (size l + size r) k v l r

-- {-# INLINABLE lookup #-}
lookup :: (HOrd k, HOrdHet k) => k ix -> HMap k v -> Maybe (v ix)
lookup _ HNil                        = Nothing
lookup k (HNode _ _ k' v left right) =
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

domain :: forall k v. (LVar k) => HMap k v -> [L.LDomain k]
domain m = go m []
  where
    go :: HMap k v -> [L.LDomain k] -> [L.LDomain k]
    go HNil xs                       = xs
    go (HNode _ _ x _ left right) xs = go left $ L.getDomain x : go right xs

keys :: forall k v. HMap k v -> [Some k]
keys m = go m []
  where
    go :: HMap k v -> [Some k] -> [Some k]
    go HNil                       xs = xs
    go (HNode _ _ k _ left right) xs = go left $ Some k : go right xs

toList :: forall k v. HMap k v -> [Some (k :*: v)]
toList m = go m []
  where
    go :: HMap k v -> [Some (k :*: v)] -> [Some (k :*: v)]
    go HNil                       xs = xs
    go (HNode _ _ k v left right) xs = go left $ Some (k :*: v) : go right xs
