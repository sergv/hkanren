----------------------------------------------------------------------------
-- |
-- Module      :  Language.DSKanren.Subst
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
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverlappingInstances      #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

module Language.HKanren.Subst
  ( Subst
  , extend
  , lookup
  , lookupVar
  -- , delete -- TODO
  , domain
  , empty
  , LVar
  , mkLVar
  -- , mkLVarType
  -- , suc
  -- , suc'
  , Term
  , ClosedTerm
  , TypeI(..)

  , If
  , Equal
  )
where

import Data.HMap (HMap)
import qualified Data.HMap as HM
import Data.HOrdering
import Data.HUtils
import Data.Monoid
import Data.Singletons
import Data.Singletons.Prelude.Bool
import Data.Type.Equality

import Prelude hiding (lookup)

type ClosedTerm h = HFix h
-- type Type t = ClosedTerm (TypeOf t)
type Term h = HFree h (LVar h)


-- type family If (c :: Bool) (t :: k) (f :: k) :: k where
--   If 'True t f = t
--   If 'False t f = f

-- type family Or (a :: Bool) (b :: Bool) :: Bool where
--   Or x y = If x 'True y

type family Equal (a :: *) (b :: *) :: Bool where
  Equal x x = 'True
  Equal x y = 'False

class TypeI (a :: (* -> *)) (ix :: *) where
  type SupportsIx a ix :: Bool
  data Type a :: * -> *
  singType :: Type a ix


-- instance (TypeI f ix) => TypeI (HFix f) ix where
--   data Type (HFix f) ix where
--     THFix :: Type f ix -> Type (HFix f) ix
--   singType = THFix singType

instance (TypeI (f (HFree f a)) ix) => TypeI (HFree f a) ix where
  type SupportsIx (HFree f a) ix = SupportsIx (f (HFree f a)) ix
  data Type (HFree f a) ix where
    -- THPure :: Type a ix -> Type (HFree f a) ix
    THFree :: Type (f (HFree f a)) ix -> Type (HFree f a) ix
  singType = THFree singType

instance (HEq (Type (f (HFree f a)))) => HEq (Type (HFree f a)) where
  heq (THFree x) (THFree y) = heq x y

instance (HEqHet (Type (f (HFree f a)))) => HEqHet (Type (HFree f a)) where
  heqIx (THFree x) (THFree y) = heqIx x y

instance (HOrd (Type (f (HFree f a)))) => HOrd (Type (HFree f a)) where
  hcompare (THFree x) (THFree y) = hcompare x y

instance (HOrdHet (Type (f (HFree f a)))) => HOrdHet (Type (HFree f a)) where
  hcompareIx (THFree x) (THFree y) = hcompareIx x y

-- instance (TypeI (f r) ix, TypeI (g r) ix, SingI (SupportsIx (f r) ix)) => TypeI ((:+:) f g r) ix where
instance (If (SupportsIx (f r) ix) (TypeI (f r) ix) (TypeI (g r) ix), SingI (SupportsIx (f r) ix)) => TypeI ((:+:) f g r) ix where
  type SupportsIx ((:+:) f g r) ix = (SupportsIx (f r) ix) :|| (SupportsIx (g r) ix)
  data Type ((:+:) f g r) ix where
    TSum ::
      (SingI (SupportsIx (f r) ix)) =>
      If (SupportsIx (f r) ix) (Type (f r) ix) (Type (g r) ix) -> Type ((:+:) f g r) ix
  singType =
    case sing :: SBool (SupportsIx (f r) ix) of
      STrue  -> TSum singType
      SFalse -> TSum singType
    -- TSum singType

instance (HEq (Type (f r)), HEq (Type (g r))) => HEq (Type ((:+:) f g r)) where
  heq :: forall ix. Type ((:+:) f g r) ix -> Type ((:+:) f g r) ix -> Bool
  heq (TSum x) (TSum x') =
    case sing :: SBool (SupportsIx (f r) ix) of
      STrue  -> heq x x'
      SFalse -> heq x x'

instance (HEqHet (Type (f r)), HEqHet (Type (g r))) => HEqHet (Type ((:+:) f g r)) where
  heqIx :: forall ix ix'. Type ((:+:) f g r) ix -> Type ((:+:) f g r) ix' -> Maybe (ix :~: ix')
  heqIx (TSum x) (TSum x') =
    case (sing :: SBool (SupportsIx (f r) ix), sing :: SBool (SupportsIx (f r) ix')) of
      (STrue,  STrue)  -> heqIx x x'
      (SFalse, SFalse) -> heqIx x x'
      _                -> Nothing

instance (HOrd (Type (f r)), HOrd (Type (g r))) => HOrd (Type ((:+:) f g r)) where
  hcompare :: forall ix. Type ((:+:) f g r) ix -> Type ((:+:) f g r) ix -> Ordering
  hcompare (TSum x) (TSum x') =
    case sing :: SBool (SupportsIx (f r) ix) of
      STrue  -> hcompare x x'
      SFalse -> hcompare x x'

instance (HOrdHet (Type (f r)), HOrdHet (Type (g r))) => HOrdHet (Type ((:+:) f g r)) where
  hcompareIx :: forall ix ix'. Type ((:+:) f g r) ix -> Type ((:+:) f g r) ix' -> HOrdering ix ix'
  hcompareIx (TSum x) (TSum x') =
    case (sing :: SBool (SupportsIx (f r) ix), sing :: SBool (SupportsIx (f r) ix')) of
      (STrue,  STrue)  -> hcompareIx x x'
      (SFalse, SFalse) -> hcompareIx x x'
      (STrue,  SFalse) -> HGT
      (SFalse, STrue)  -> HLT

-- | Logic variable.
data LVar (f :: (* -> *) -> (* -> *)) ix where
  LVar :: Integer -> Type (f (Term f)) ix -> LVar f ix
  -- deriving (Show, Eq, Ord)

instance HEq (LVar h) where
  -- heq :: (Eq (Type ix)) => LVar h ix -> LVar h ix -> Bool
  -- heq (LVar n x) (LVar m y) = n == m && (==) x y
  heq (LVar n _) (LVar m _) = n == m

instance (HEqHet (Type (h (Term h)))) => HEqHet (LVar h) where
  heqIx (LVar _ x) (LVar _ y) = heqIx x y

-- instance HOrd (LVar h) where
--   hcompare (LVar n _) (LVar m _) = compare n m

instance (HOrd (Type (h (Term h)))) => HOrd (LVar h) where
  hcompare (LVar n x) (LVar m y) = hcompare x y <> compare n m

instance (HOrdHet (Type (h (Term h)))) => HOrdHet (LVar h) where
  hcompareIx (LVar _ x) (LVar _ y) = hcompareIx x y

instance HShow (LVar f) where
  hshowsPrec n (LVar m _) = \xs -> showParen (n == 11) (\ys -> "LVar " ++ show m ++ ys) xs

-- suc :: LVar h ix -> LVar h ix
-- suc (LVar n x) = LVar (n + 1) x
--
-- suc' :: (HFunctor h) => LVar h ix -> h f ix' -> LVar h ix'
-- suc' (LVar n _) y = LVar (n + 1) $ hfmap (const $ K ()) y

mkLVar :: (TypeI (h (Term h)) ix) => Integer -> LVar h ix
mkLVar n = LVar n singType

-- mkLVarType :: (TypeRep h) => Integer -> Type h ix -> LVar h ix
-- mkLVarType n t = LVar n t

newtype Subst h = Subst (HMap (LVar h) (Term h))

lookup :: (HOrd (Type (h (Term h))), HOrdHet (Type (h (Term h)))) => LVar h ix -> Subst h -> Maybe (Term h ix)
lookup k (Subst s) = HM.lookup k s

lookupVar :: Integer -> Subst h -> Maybe (Some (Term h))
lookupVar n (Subst s) = HM.lookupWith (\(LVar m _) -> compare n m) s

extend :: (HOrd (Type (h (Term h))), HOrdHet (Type (h (Term h)))) => LVar h ix -> Term h ix -> Subst h -> Subst h
extend k v (Subst s) = Subst $ HM.insert k v s

domain :: Subst h -> [Some (LVar h)]
domain (Subst s) = HM.keys s

empty :: Subst t
empty = Subst HM.empty


