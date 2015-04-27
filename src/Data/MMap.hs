----------------------------------------------------------------------------
-- |
-- Module      :  Data.MMap
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

module Data.MMap
  (MMap)
where

import Control.Applicative
import Data.GMap (GMap(..))
import Data.HUtils
import Data.Map (Map)
import qualified Data.Map as M

import Unsafe.Coerce

import Language.HKanren.LVar (LVar(..), Term, TypeI(..), mkLVar')

newtype MMap h = MMap (Map Integer (Some (Term h :*: Type (h (Term h)))))

instance GMap (MMap h) where
  type GMapKey (MMap h) = LVar h
  type GMapVal (MMap h) = Term h
  type GMapDomain (MMap h) = Integer
  empty = MMap M.empty
  size (MMap m) = M.size m
  insert (LVar n typ) t (MMap m) = MMap $ M.insert n (Some (t :*: typ)) m
  lookup (LVar n _) (MMap m) = fixTermIndex <$> M.lookup n m
    where
      fixTermIndex :: Some (Term h :*: a) -> Term h ix
      fixTermIndex (Some (t :*: _)) = unsafeCoerce t
  domain (MMap m) = M.keys m
  keys (MMap m)   = map (\(k, Some (_ :*: typ)) -> Some $ mkLVar' k typ) $ M.toList m
  toList (MMap m) = map (\(k, Some (v :*: typ)) -> (Some $ mkLVar' k typ :*: v)) $ M.toList m
