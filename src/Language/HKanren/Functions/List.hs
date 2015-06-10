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
  , memberp
  , notMember
  , allo
  , foldlo
  , foldlo'
  , foldl2o
  , foldl2o'
  )
where

import Data.HUtils
import Language.HKanren.Syntax
import Language.HKanren.Types.List

import Prelude (return, ($), Int, fromInteger, (*))

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

memberp
  :: forall k ix. (ListF :<: LFunctor k, TypeI (Term1 k) ix, TypeI (Term1 k) (List ix))
  => Term k ix -> Term k (List ix) -> Predicate k
memberp x xs =
  (fresh $ \y ys -> do
    xs ==^ Cons y ys
    condp
      ( (2 * one)
      , x === y)
      ( one
      , do x =/= y
           memberp x ys))
  where
    one :: Int
    one = 1

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

foldlo'
  :: forall k acc ix. (ListF :<: LFunctor k, TypeI (Term1 k) acc, TypeI (Term1 k) ix, TypeI (Term1 k) (List ix))
  => Term k acc
  -> Term k (List ix)
  -> Term k acc
  -> (Term k acc -> Term k ix -> Term k acc -> Predicate k)
  -> Predicate k
foldlo' acc xs out f = foldlo f acc xs out


foldl2o
  :: forall k acc acc' ix.
     (ListF :<: LFunctor k, TypeI (Term1 k) acc, TypeI (Term1 k) acc', TypeI (Term1 k) ix, TypeI (Term1 k) (List ix))
  => (Term k acc -> Term k acc' -> Term k ix -> Term k acc -> Term k acc' -> Predicate k)
  -> Term k acc
  -> Term k acc'
  -> Term k (List ix)
  -> Term k acc
  -> Term k acc'
  -> Predicate k
foldl2o f acc acc' xs out out' =
  conde
    (do xs   ==^ Nil
        acc  === out
        acc' === out')
    (fresh $ \y ys out1 out2 -> do
      xs ==^ Cons y ys
      f acc acc' y out1 out2
      foldl2o f out1 out2 ys out out')


foldl2o'
  :: forall k acc acc' ix.
     (ListF :<: LFunctor k, TypeI (Term1 k) acc, TypeI (Term1 k) acc', TypeI (Term1 k) ix, TypeI (Term1 k) (List ix))
  => Term k acc
  -> Term k acc'
  -> Term k (List ix)
  -> Term k acc
  -> Term k acc'
  -> (Term k acc -> Term k acc' -> Term k ix -> Term k acc -> Term k acc' -> Predicate k)
  -> Predicate k
foldl2o' acc acc' xs out out' f =
  foldl2o f acc acc' xs out out'
