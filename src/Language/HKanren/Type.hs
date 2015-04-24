----------------------------------------------------------------------------
-- |
-- Module      :  Language.HKanren.Type
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

module Language.HKanren.Type where

import Data.HOrdering
import Data.HUtils
import Data.Singletons
import Data.Singletons.Prelude.Bool
import Data.Type.Equality


type family Equal (a :: *) (b :: *) :: Bool where
  Equal x x = 'True
  Equal x y = 'False

class TypeI (a :: (* -> *)) (ix :: *) where
  type SupportsIx a ix :: Bool
  data Type a :: * -> *
  singType :: Type a ix

typeOf :: (TypeI a ix) => p ix -> Type a ix
typeOf _ = singType

instance (TypeI (f (HFree f a)) ix) => TypeI (HFree f a) ix where
  type SupportsIx (HFree f a) ix = SupportsIx (f (HFree f a)) ix
  data Type (HFree f a) ix where
    -- No THPure case because my "a" depends on "f" anyway and, in any case,
    -- "f" is our main functor that defines types.
    -- THPure :: Type a ix -> Type (HFree f a) ix
    THFree :: Type (f (HFree f a)) ix -> Type (HFree f a) ix
  {-# INLINABLE singType #-}
  singType = THFree singType

instance (HEq (Type (f (HFree f a)))) => HEq (Type (HFree f a)) where
  {-# INLINABLE heq #-}
  heq (THFree x) (THFree y) = heq x y

instance (HEqHet (Type (f (HFree f a)))) => HEqHet (Type (HFree f a)) where
  {-# INLINABLE heqIx #-}
  heqIx (THFree x) (THFree y) = heqIx x y

instance (HOrd (Type (f (HFree f a)))) => HOrd (Type (HFree f a)) where
  {-# INLINABLE hcompare #-}
  hcompare (THFree x) (THFree y) = hcompare x y

instance (HOrdHet (Type (f (HFree f a)))) => HOrdHet (Type (HFree f a)) where
  {-# INLINABLE hcompareIx #-}
  hcompareIx (THFree x) (THFree y) = {-# SCC hcompareIx_type_hfree #-} hcompareIx x y

instance (If (SupportsIx (f r) ix) (TypeI (f r) ix) (TypeI (g r) ix), SingI (SupportsIx (f r) ix)) => TypeI ((:+:) f g r) ix where
  type SupportsIx ((:+:) f g r) ix = (SupportsIx (f r) ix) :|| (SupportsIx (g r) ix)
  data Type ((:+:) f g r) ix where
    TSum ::
      (SingI (SupportsIx (f r) ix)) =>
      If (SupportsIx (f r) ix) (Type (f r) ix) (Type (g r) ix) -> Type ((:+:) f g r) ix
  {-# INLINABLE singType #-}
  singType =
    case sing :: SBool (SupportsIx (f r) ix) of
      STrue  -> TSum singType
      SFalse -> TSum singType

instance (HEq (Type (f r)), HEq (Type (g r))) => HEq (Type ((:+:) f g r)) where
  {-# INLINABLE heq #-}
  heq :: forall ix. Type ((:+:) f g r) ix -> Type ((:+:) f g r) ix -> Bool
  heq (TSum x) (TSum x') =
    case sing :: SBool (SupportsIx (f r) ix) of
      STrue  -> heq x x'
      SFalse -> heq x x'

instance (HEqHet (Type (f r)), HEqHet (Type (g r))) => HEqHet (Type ((:+:) f g r)) where
  {-# INLINABLE heqIx #-}
  heqIx :: forall ix ix'. Type ((:+:) f g r) ix -> Type ((:+:) f g r) ix' -> Maybe (ix :~: ix')
  heqIx (TSum x) (TSum x') =
    case (sing :: SBool (SupportsIx (f r) ix), sing :: SBool (SupportsIx (f r) ix')) of
      (STrue,  STrue)  -> heqIx x x'
      (SFalse, SFalse) -> heqIx x x'
      _                -> Nothing

instance (HOrd (Type (f r)), HOrd (Type (g r))) => HOrd (Type ((:+:) f g r)) where
  {-# INLINABLE hcompare #-}
  hcompare :: forall ix. Type ((:+:) f g r) ix -> Type ((:+:) f g r) ix -> Ordering
  hcompare (TSum x) (TSum x') =
    case sing :: SBool (SupportsIx (f r) ix) of
      STrue  -> hcompare x x'
      SFalse -> hcompare x x'

instance (HOrdHet (Type (f r)), HOrdHet (Type (g r))) => HOrdHet (Type ((:+:) f g r)) where
  {-# INLINABLE hcompareIx #-}
  hcompareIx :: forall ix ix'. Type ((:+:) f g r) ix -> Type ((:+:) f g r) ix' -> HOrdering ix ix'
  hcompareIx (TSum x) (TSum x') = {-# SCC hcompareIx_type_sum #-}
    case sing :: SBool (SupportsIx (f r) ix) of
      STrue  ->
        case sing :: SBool (SupportsIx (f r) ix') of
          STrue  -> {-# SCC hcompareIx_type_sum_left #-} hcompareIx x x'
          SFalse -> HGT
      SFalse ->
        case sing :: SBool (SupportsIx (f r) ix') of
          STrue  -> HLT
          SFalse -> {-# SCC hcompareIx_type_sum_right #-} hcompareIx x x'
    -- case (sing :: SBool (SupportsIx (f r) ix), sing :: SBool (SupportsIx (f r) ix')) of
    --   (STrue,  STrue)  -> hcompareIx x x'
    --   (SFalse, SFalse) -> hcompareIx x x'
    --   (STrue,  SFalse) -> HGT
    --   (SFalse, STrue)  -> HLT

