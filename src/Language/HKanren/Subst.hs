----------------------------------------------------------------------------
-- |
-- Module      :  Language.DSKanren.Subst
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE UndecidableInstances      #-}

module Language.HKanren.Subst
  ( Subst
  , extend
  , lookup
  , domain
  , domainSize
  , empty
  , LVar
  , L.mkLVar
  , Term
  , Term1
  , LFunctor
  , LDomain
  , LMap
  , L.getDomain
  , TypeI(..)
  , If
  , Equal
  , typeOf
  )
where

import Data.HOrdering
import Data.Singletons.Prelude.Bool

import Language.HKanren.LVar (LVar, LDomain, LMap, LFunctor, Term, Term1)
import qualified Language.HKanren.LVar as L
import Language.HKanren.Type

import Prelude hiding (lookup)

-- type LVarMap m h = (GMap m, G.GMapKey m ~ (LVar h), G.GMapVal m ~ (Term h))

newtype Subst (k :: * -> *) = Subst (LMap k)

instance (Show (LMap k)) => Show (Subst k) where
  showsPrec n (Subst m) = showsPrec n m

lookup :: (HOrdHet (Type (Term1 k)), LVar k) => k ix -> Subst k -> Maybe (Term k ix)
lookup k (Subst s) = L.lookup k s

extend :: (HOrdHet (Type (Term1 k)), LVar k) => k ix -> Term k ix -> Subst k -> Subst k
extend k v (Subst s) = Subst $ L.insert k v s

domain :: (LVar k) => Subst k -> [LDomain k]
domain (Subst s) = L.domain s

domainSize :: (LVar k) => Subst k -> LDomain k
domainSize (Subst m) = L.size m

empty :: (LVar k) => Subst k
empty = Subst L.empty
