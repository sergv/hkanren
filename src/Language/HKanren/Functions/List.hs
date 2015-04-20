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

module Language.HKanren.Functions.List where

import Data.HUtils
import Language.HKanren.Syntax
import Language.HKanren.Types.List

import Prelude (return, ($))

-- redefine the syntax
(>>) :: Predicate h -> Predicate h -> Predicate h
(>>) = conj

(>>=) :: (TypeI (h (Term h)) ix)
      => Fresh ix
      -> (Term h ix -> Predicate h)
      -> Predicate h
(>>=) = fresh

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


