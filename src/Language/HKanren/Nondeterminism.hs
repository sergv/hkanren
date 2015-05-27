----------------------------------------------------------------------------
-- |
-- Module      :  Language.HKanren.Nondeterminism
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

module Language.HKanren.Nondeterminism
  ( nondetLogicT
  , nondetDepthFirst
  , nondetBreadthFirst
  , nondetBreadthFirstRandomized
  , nondetIterativeDeepeningBreadthFirst
  , NondetLogicT
  , NondetDepthFirst
  , NondetBreadthFirst
  , NondetBreadthFirstRandomized
  , NondetIterativeDeepeningBreadthFirst
  )
where

import Control.Monad.SFK
import Control.Monad.ContNondet
import Control.Monad.Reader
import Control.Monad.State
import Data.Bounded
import Data.DiffList
import Data.Levels
import Data.Proxy
import Data.Random.Source.PureMT (PureMT)

import Prelude hiding (Bounded)

type NondetLogicT = SFK
type NondetDepthFirst = ContNondet DiffList
type NondetBreadthFirst = ContNondet (Levels DiffList)
type NondetBreadthFirstRandomized = ContNondetT (Levels DiffList) (State PureMT)
type NondetIterativeDeepeningBreadthFirst = ContNondetT (Bounded DiffList) (Reader Int)

nondetLogicT :: Proxy NondetLogicT
nondetLogicT = Proxy

nondetDepthFirst :: Proxy NondetDepthFirst
nondetDepthFirst = Proxy

nondetBreadthFirst :: Proxy NondetBreadthFirst
nondetBreadthFirst = Proxy

nondetBreadthFirstRandomized :: Proxy NondetBreadthFirstRandomized
nondetBreadthFirstRandomized = Proxy

nondetIterativeDeepeningBreadthFirst :: Proxy NondetIterativeDeepeningBreadthFirst
nondetIterativeDeepeningBreadthFirst = Proxy
