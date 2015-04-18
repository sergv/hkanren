----------------------------------------------------------------------------
-- |
-- Module      :  Language.HKanren.SingletonsPlayground
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# LANGUAGE EmptyCase #-}

module Language.HKanren.SingletonsPlayground where

import Data.Singletons
import Data.Singletons.Prelude.Bool
import Data.Singletons.Decide
import Data.Singletons.Prelude.Eq
import Data.Singletons.TH
-- import Data.Type.Equality

data Nat = Z | S Nat
  deriving (Eq)

data instance Sing (n :: Nat) where
  SZ :: Sing Z
  SS :: Sing n -> Sing (S n)

type SNat (k :: Nat) = Sing k

class (proxy ~ ('KProxy :: KProxy k)) => SEqIx (proxy :: KProxy k) where
  sEqIx :: forall (a :: k) b. Sing a -> Sing b -> Maybe (a :~: b)

instance SEqIx ('KProxy :: KProxy Nat) where
  sEqIx SZ     SZ     = Just Refl
  sEqIx SZ     (SS _) = Nothing
  sEqIx (SS _) SZ     = Nothing
  sEqIx (SS x) (SS y) =
    case sEqIx x y of
      Just Refl -> Just Refl
      Nothing   -> Nothing

-- instance SDecide ('KProxy :: KProxy Nat) where
--   (%~) SZ     SZ      = Proved Refl
--   (%~) SZ     (SS _)  =
--   (%~) (SS n) (SS n') =
--     case n %~ n' of
--       Proved Refl -> Proved Refl

-- $(singletons [d|
--   data Nat = Z | S Nat
--     deriving (Eq)
--   |])

$(singletons [d|
  data Test = Simple | Complex Test Test
    deriving (Eq)
  |])

instance SEqIx ('KProxy :: KProxy Test) where
  sEqIx SSimple          SSimple          = Just Refl
  sEqIx SSimple          (SComplex _ _)   = Nothing
  sEqIx (SComplex _ _)   SSimple          = Nothing
  sEqIx (SComplex xl xr) (SComplex yl yr) =
    case sEqIx xl yl of
      Just Refl ->
        case sEqIx xr yr of
          Just Refl -> Just Refl
          Nothing   -> Nothing
      Nothing   -> Nothing



foo :: SNat (S (S Z))
foo = SS $ SS SZ

bar :: STest (Complex Simple (Complex Simple Simple))
bar = SComplex SSimple $ SComplex SSimple SSimple

main :: IO ()
main = do
  -- print $ sEqIx foo bar
  return ()
