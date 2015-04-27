----------------------------------------------------------------------------
-- |
-- Module      :  Data.GMap
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
-- Generic map.
----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}

module Language.HKanren.LVar where

import Data.HOrdering
import Data.HUtils
import Language.HKanren.Type

-- import Language.HKanren.Type

-- class (HOrd (k f), HOrdHet (k f), HShow (k f), HPretty (k f)) => LVar (k :: ((* -> *) -> (* -> *)) -> * -> *) f where
--   -- type Term h = HFree h k
--   mkLVar :: Integer -> Type (f (HFree f (k f))) ix -> k f ix

type Term k  = HFree (LFunctor k) k
type Term1 k = LFunctor k (Term k)

class (HOrd k, HOrdHet k, HShow k, HPretty k) => LVar (k :: * -> *) where
  type LFunctor k :: (* -> *) -> (* -> *)
  type LDomain k  :: *
  data LMap k     :: *
  mkLVar    :: (TypeI (Term1 k) ix) => Integer -> k ix
  getDomain :: k ix -> LDomain k

  empty  :: LMap k
  size   :: LMap k -> LDomain k
  insert :: k ix -> Term k ix -> LMap k -> LMap k
  lookup :: k ix -> LMap k -> Maybe (Term k ix)
  -- ^ specialized version of keys, for efficiency
  domain :: LMap k -> [LDomain k]
  keys   :: LMap k -> [Some k]
  toList :: LMap k -> [Some (k :*: Term k)]
