----------------------------------------------------------------------------
-- |
-- Module      :  Data.HOrd
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds      #-}
{-# LANGUAGE TypeOperators  #-}

module Data.HOrdering where

import Data.Type.Equality

class HEq (h :: * -> *) where
  heq :: h ix -> h ix -> Bool

class (HEq h) => HEqHet (h :: * -> *) where
  heqIx :: h ix -> h ix' -> Maybe (ix :~: ix')

  (==*) :: h ix -> h ix' -> Bool
  (==*) x y =
    case heqIx x y of
      Just Refl -> heq x y
      Nothing   -> False

class (HEq h) => HOrd (h :: * -> *) where
  hcompare :: h ix -> h ix -> Ordering

data HOrdering ix ix' where
  HLT :: HOrdering ix ix'
  HEQ :: HOrdering ix ix
  HGT :: HOrdering ix ix'

hordering2ordering :: HOrdering ix ix' -> Ordering
hordering2ordering HLT = LT
hordering2ordering HEQ = EQ
hordering2ordering HGT = GT

-- What to return when two indices are just not equal, but it's unknown which one
-- is greater?
class (HEqHet h, HOrd h) => HOrdHet (h :: * -> *) where
  hcompareIx :: h ix -> h ix' -> HOrdering ix ix'

  hcompareHet :: h ix -> h ix' -> Ordering
  hcompareHet x y =
    case hcompareIx x y of
      HLT -> LT
      HEQ -> hcompare x y
      HGT -> GT
