----------------------------------------------------------------------------
-- |
-- Module      :  BenchmarkLVars
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators    #-}

module BenchmarkLVars where

import Control.Exception
import Control.Monad
import Data.HOrdering
import Data.HUtils
import System.Directory
import System.FilePath

import Criterion.Main
import Criterion.Types

import Language.HKanren.Functions.List (appendo)
import Language.HKanren.Types.List (ListF, List, list)
import LispLists

import Language.HKanren.Syntax
import qualified Language.HKanren.IntLVar as IntLVar
import qualified Language.HKanren.IntegerLVar as IntegerLVar
import qualified Language.HKanren.SafeLVar as SafeLVar

type SafeTerm    = Term (SafeLVar.LVar LispTermF)
type IntegerTerm = Term (IntegerLVar.LVar LispTermF)
type IntTerm     = Term (IntLVar.LVar LispTermF)

fSafe :: (SafeTerm (List (List Atom)), SafeTerm (List (List Atom))) -> SafeTerm (List (List Atom))
fSafe = f
fInteger :: (IntegerTerm (List (List Atom)), IntegerTerm (List (List Atom))) -> IntegerTerm (List (List Atom))
fInteger = f
fInt :: (IntTerm (List (List Atom)), IntTerm (List (List Atom))) -> IntTerm (List (List Atom))
fInt = f

{-# INLINABLE f #-}
f :: (LVar k, TypeI (Term1 k) ix, TypeI (Term1 k) (List ix), Unifiable (LFunctor k) k, ListF :<: LFunctor k, HFunctorId (LFunctor k), HFoldable (LFunctor k), HShow (Term1 k), HOrdHet (Type (Term1 k)), HOrdHet (Term1 k), Ord (LDomain k)) => (Term k (List ix), Term k (List ix)) -> Term k (List ix)
f (ys, zs) =
  case runN 1 $ \q -> appendo q ys zs of
    []         -> error "no results"
    ((x, _):_) -> x

makeList :: (LVar k, TypeI (Term1 k) Atom, TypeI (Term1 k) (List Atom), ListF :<: LFunctor k, AtomF :<: LFunctor k) => Int -> Term k (List (List Atom))
makeList k = list
  [ list [ iAtom ("x_" ++ show n ++ "_" ++ show m)
         | m <- [1..n]
         ]
  | n <- [k..90]
  ]

{-# INLINABLE ys #-}
ys :: (LVar k, TypeI (Term1 k) Atom, TypeI (Term1 k) (List Atom), ListF :<: LFunctor k, AtomF :<: LFunctor k) => Term k (List (List Atom))
ys = makeList 75

{-# INLINABLE zs #-}
zs :: (LVar k, TypeI (Term1 k) Atom, TypeI (Term1 k) (List Atom), ListF :<: LFunctor k, AtomF :<: LFunctor k) => Term k (List (List Atom))
zs = makeList 1

ysSafe :: SafeTerm (List (List Atom))
ysSafe = ys
zsSafe :: SafeTerm (List (List Atom))
zsSafe = zs

ysInteger :: IntegerTerm (List (List Atom))
ysInteger = ys
zsInteger :: IntegerTerm (List (List Atom))
zsInteger = zs

ysInt :: IntTerm (List (List Atom))
ysInt = ys
zsInt :: IntTerm (List (List Atom))
zsInt = zs

main :: IO ()
main = do
  tmpDir <- getTemporaryDirectory
  let config = defaultConfig { forceGC    = True
                             , reportFile = Just $ tmpDir </> "benchmark-lvars.html"
                             , resamples  = 10000
                             }

  void $ evaluate $ hrnf $ ysSafe
  void $ evaluate $ hrnf $ zsSafe
  void $ evaluate $ hrnf $ ysInteger
  void $ evaluate $ hrnf $ zsInteger
  void $ evaluate $ hrnf $ ysInt
  void $ evaluate $ hrnf $ zsInt
  defaultMainWith config [
      bench "safe lvars"    $ whnf (hrnf . fSafe) (ysSafe, zsSafe)
    , bench "integer lvars" $ whnf (hrnf . fInteger) (ysInteger, zsInteger)
    , bench "int lvars"     $ whnf (hrnf . fInt) (ysInt, zsInt)
    ]
