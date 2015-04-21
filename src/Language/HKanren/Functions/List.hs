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

import Prelude (return, ($))

-- redefine the syntax
(>>) :: Predicate h -> Predicate h -> Predicate h
(>>) = conj

-- (>>=) :: (TypeI (h (Term h)) ix)
--       => Fresh ix
--       -> (Term h ix -> Predicate h)
--       -> Predicate h
-- (>>=) = fresh

appendo
  :: (ListF :<: h, TypeI (h (Term h)) (List ix), TypeI (h (Term h)) ix)
  => Term h (List ix)
  -> Term h (List ix)
  -> Term h (List ix)
  -> Predicate h
appendo l r o =
  conde
    (do l ==^ Nil
        o === r)
    (manyFresh $ \h t o' -> do
       Cons h t  ^== l
       appendo t r o'
       Cons h o' ^== o)

allUnique
  :: forall h ix. (ListF :<: h, TypeI (h (Term h)) ix, TypeI (h (Term h)) (List ix))
  => Term h (List ix) -> Predicate h
allUnique args =
  conde
    (args ==^ Nil)
    (manyFresh $ \x xs -> do
      args ==^ Cons x xs
      notMember x xs
      allUnique xs)

member
  :: forall h ix. (ListF :<: h, TypeI (h (Term h)) ix, TypeI (h (Term h)) (List ix))
  => Term h ix -> Term h (List ix) -> Predicate h
member x xs =
  (manyFresh $ \y ys -> do
    xs ==^ Cons y ys
    conde
      (x === y)
      (do x =/= y
          member x ys))

notMember
  :: forall h ix. (ListF :<: h, TypeI (h (Term h)) ix, TypeI (h (Term h)) (List ix))
  => Term h ix -> Term h (List ix) -> Predicate h
notMember x xs =
  conde
    (xs ==^ Nil)
    (manyFresh $ \y ys -> do
      xs ==^ Cons y ys
      x =/= y
      notMember x ys)

allo
  :: forall h ix. (ListF :<: h, TypeI (h (Term h)) ix, TypeI (h (Term h)) (List ix))
  => (Term h ix -> Predicate h) -> Term h (List ix) -> Predicate h
allo p xs =
  conde
    (xs ==^ Nil)
    (manyFresh $ \y ys -> do
      xs ==^ Cons y ys
      p y
      allo p ys)

foldlo
  :: forall h acc ix. (ListF :<: h, TypeI (h (Term h)) acc, TypeI (h (Term h)) ix, TypeI (h (Term h)) (List ix))
  => (Term h acc -> Term h ix -> Term h acc -> Predicate h)
  -> Term h acc
  -> Term h (List ix)
  -> Term h acc
  -> Predicate h
foldlo f acc xs out =
  conde
    (do xs  ==^ Nil
        acc === out)
    (manyFresh $ \y ys out' -> do
      xs ==^ Cons y ys
      f acc y out'
      foldlo f out' ys out)
