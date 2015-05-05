----------------------------------------------------------------------------
-- |
-- Module      :  Language.HKanren.Functions.Nat
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RebindableSyntax    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}

module Language.HKanren.Functions.Nat
  ( pluso
  , plus1
  , plus3o
  )
where

import Data.HUtils
import Language.HKanren.Syntax
import Language.HKanren.Types.Nat

import Prelude (return, fail, ($), show)

import Data.String

pluso
  :: (NatF :<: LFunctor k, TypeI (Term1 k) Nat)
  => Term k Nat
  -> Term k Nat
  -> Term k Nat
  -> Predicate k
pluso x y z = do
  conde
    (do
      x ==^ Z
      y === z)
    -- (do
    --   y ==^ Z
    --   x === z)
    (fresh $ \x' z' -> do
      x ==^ S x'
      z ==^ S z'
      pluso x' y z')

plus1
  :: (NatF :<: LFunctor k, TypeI (Term1 k) Nat)
  => Term k Nat
  -> Term k Nat
  -> Predicate k
plus1 x y = y ==^ S x

plus3o
  :: (NatF :<: LFunctor k, TypeI (Term1 k) Nat)
  => Term k Nat
  -> Term k Nat
  -> Term k Nat
  -> Term k Nat
  -> Predicate k
plus3o x y z w = do
  t <- pluso x y
  pluso t z w
