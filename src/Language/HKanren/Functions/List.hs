----------------------------------------------------------------------------
-- |
-- Module      :  Language.HKanren.Functions.List
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

module Language.HKanren.Functions.List
  ( appendo
  , allUnique
  , member
  , notMember
  , allo
  , foldlo
  )
where

import Data.HUtils
import Language.HKanren.Syntax
import Language.HKanren.Types.List
import Language.HKanren.Subst (Term1, LFunctor)

import Prelude (return, ($))

-- redefine the syntax
(>>) :: Predicate k -> Predicate k -> Predicate k
(>>) = conj

-- (>>=) :: Fresh k a
--       -> (a -> Predicate k)
--       -> Predicate k
-- (>>=) = withFresh

appendo
  :: (ListF :<: LFunctor k, TypeI (Term1 k) (List ix), TypeI (Term1 k) ix)
  => Term k (List ix)
  -> Term k (List ix)
  -> Term k (List ix)
  -> Predicate k
appendo l r o =
  conde
    (do l ==^ Nil
        o === r)
    (fresh $ \h t o' -> do
      Cons h t  ^== l
      appendo t r o'
      Cons h o' ^== o)

allUnique
  :: forall k ix. (ListF :<: LFunctor k, TypeI (Term1 k) ix, TypeI (Term1 k) (List ix))
  => Term k (List ix) -> Predicate k
allUnique args =
  conde
    (args ==^ Nil)
    (fresh $ \x xs -> do
      args ==^ Cons x xs
      notMember x xs
      allUnique xs)

member
  :: forall k ix. (ListF :<: LFunctor k, TypeI (Term1 k) ix, TypeI (Term1 k) (List ix))
  => Term k ix -> Term k (List ix) -> Predicate k
member x xs =
  (fresh $ \y ys -> do
    xs ==^ Cons y ys
    conde
      (x === y)
      (do x =/= y
          member x ys))

notMember
  :: forall k ix. (ListF :<: LFunctor k, TypeI (Term1 k) ix, TypeI (Term1 k) (List ix))
  => Term k ix -> Term k (List ix) -> Predicate k
notMember x xs =
  conde
    (xs ==^ Nil)
    (fresh $ \y ys -> do
      xs ==^ Cons y ys
      x =/= y
      notMember x ys)

allo
  :: forall k ix. (ListF :<: LFunctor k, TypeI (Term1 k) ix, TypeI (Term1 k) (List ix))
  => (Term k ix -> Predicate k) -> Term k (List ix) -> Predicate k
allo p xs =
  conde
    (xs ==^ Nil)
    (fresh $ \y ys -> do
      xs ==^ Cons y ys
      p y
      allo p ys)

foldlo
  :: forall k acc ix. (ListF :<: LFunctor k, TypeI (Term1 k) acc, TypeI (Term1 k) ix, TypeI (Term1 k) (List ix))
  => (Term k acc -> Term k ix -> Term k acc -> Predicate k)
  -> Term k acc
  -> Term k (List ix)
  -> Term k acc
  -> Predicate k
foldlo f acc xs out =
  conde
    (do xs  ==^ Nil
        acc === out)
    (fresh $ \y ys out' -> do
      xs ==^ Cons y ys
      f acc y out'
      foldlo f out' ys out)
