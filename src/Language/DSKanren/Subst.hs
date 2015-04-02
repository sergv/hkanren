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

module Language.DSKanren.Subst
  ( Subst
  , extend
  , lookup
  , delete
  , domain
  , empty
  , Var
  , initV
  , suc
  )
where

import Data.Map (Map)
import qualified Data.Map as M

import Prelude hiding (lookup)

-- | The abstract type of variables. As a consumer you should never
-- feel the urge to manipulate these directly.
newtype Var = V Integer deriving (Eq, Ord)

initV :: Var
initV = V 0

instance Show Var where
  show (V i) = '_' : show i

suc :: Var -> Var
suc (V i) = V (i + 1)

-- type Subst = Map Var Term
newtype Subst t = Subst (Map Var t)
  deriving (Show, Eq, Ord)

lookup :: Var -> Subst t -> Maybe t
lookup k (Subst s) = M.lookup k s

delete :: Var -> Subst t -> Subst t
delete k (Subst s) = Subst $ M.delete k s

-- | Extend an environment with a given term. Note that
-- that we don't even bother to canonize things here, that
-- can wait until we extact a solution.
extend :: Var -> t -> Subst t  -> Subst t
extend k v (Subst s) = Subst $ M.insert k v s

domain :: Subst t -> [Var]
domain (Subst s) = M.keys s

empty :: Subst t
empty = Subst M.empty
