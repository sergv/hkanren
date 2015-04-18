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
{-# LANGUAGE PolyKinds                 #-}
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
  , SingI(..)
  , SingOpt(..)

  , If
  , Or
  , Equal
  )
where

import Control.Applicative hiding (empty)
import Data.HMap (HMap)
import qualified Data.HMap as HM
import Data.HOrdering
import Data.HUtils
import Data.Monoid
import Data.Type.Equality

import Prelude hiding (lookup)

type ClosedTerm h = HFix h
-- type Type t = ClosedTerm (TypeOf t)
type Term h = HFree h (LVar h)


type family If (c :: Bool) (t :: k) (f :: k) :: k where
  If 'True t f = t
  If 'False t f = f

type family Or (a :: Bool) (b :: Bool) :: Bool where
  Or x y = If x 'True y

type family Equal (a :: k) (b :: k) :: Bool

class SingI (a :: k) (ix :: *) where
  type SupportsIx a ix :: Bool
  data Sing a :: * -> *
  sing :: Sing a ix

class SingOpt (a :: k) (ix :: *) where
  singOpt :: Maybe (Sing a ix)

-- instance (SingI f ix) => SingI (HFix f) ix where
--   data Sing (HFix f) ix where
--     THFix :: Sing f ix -> Sing (HFix f) ix
--   sing = THFix sing

instance (SingI (f (HFree f a)) ix) => SingI (HFree f a) ix where
  type SupportsIx (HFree f a) ix = SupportsIx (f (HFree f a)) ix
  data Sing (HFree f a) ix where
    -- THPure :: Sing a ix -> Sing (HFree f a) ix
    THFree :: Sing (f (HFree f a)) ix -> Sing (HFree f a) ix
  sing = THFree sing

instance (HEq (Sing (f (HFree f a)))) => HEq (Sing (HFree f a)) where
  heq (THFree x) (THFree y) = heq x y

instance (HEqHet (Sing (f (HFree f a)))) => HEqHet (Sing (HFree f a)) where
  heqIx (THFree x) (THFree y) = heqIx x y

instance (HOrd (Sing (f (HFree f a)))) => HOrd (Sing (HFree f a)) where
  hcompare (THFree x) (THFree y) = hcompare x y

instance (HOrdHet (Sing (f (HFree f a)))) => HOrdHet (Sing (HFree f a)) where
  hcompareIx (THFree x) (THFree y) = hcompareIx x y

instance (SingI (f r) ix, SingOpt (g r) ix) => SingI ((:+:) f g r) ix where
  type SupportsIx ((:+:) f g r) ix = Or (SupportsIx (f r) ix) (SupportsIx (g r) ix)
  data Sing ((:+:) f g r) ix where
    TInl :: Sing (f r) ix -> Sing ((:+:) f g r) ix
    TInr :: Sing (g r) ix -> Sing ((:+:) f g r) ix
  sing =
    case singOpt :: Maybe (Sing (g r) ix) of
      Just x  -> TInr x
      Nothing -> TInl sing

instance (SingOpt (f r) ix, SingOpt (g r) ix) => SingOpt ((:+:) f g r) ix where
  singOpt =
    case singOpt :: Maybe (Sing (f r) ix) of
      Just x  -> Just $ TInl x
      Nothing -> TInr <$> singOpt

-- instance (SingOpt (f r) ix, SingOpt (g r) ix) => SingI ((:+:) f g r) ix where
--   data Sing ((:+:) f g r) ix where
--     TInl :: Sing (f r) ix -> Sing ((:+:) f g r) ix
--     TInr :: Sing (g r) ix -> Sing ((:+:) f g r) ix
--   sing =
--     case singOpt :: Maybe (Sing (f r) ix) of
--       Just x  -> TInl x
--       Nothing ->
--         case singOpt :: Maybe (Sing (g r) ix) of
--           Just y  -> TInr y
--           Nothing -> error "impossible"


instance (HEq (Sing (f r)), HEq (Sing (g r))) => HEq (Sing ((:+:) f g r)) where
  heq (TInl x) (TInl x') = heq x x'
  heq (TInr y) (TInr y') = heq y y'
  heq _        _         = False

instance (HEqHet (Sing (f r)), HEqHet (Sing (g r))) => HEqHet (Sing ((:+:) f g r)) where
  heqIx (TInl x) (TInl x') = heqIx x x'
  heqIx (TInr y) (TInr y') = heqIx y y'
  heqIx _        _         = Nothing

instance (HOrd (Sing (f r)), HOrd (Sing (g r))) => HOrd (Sing ((:+:) f g r)) where
  hcompare (TInl x) (TInl x') = hcompare x x'
  hcompare (TInl _) (TInr _)  = LT
  hcompare (TInr y) (TInr y') = hcompare y y'
  hcompare (TInr _) (TInl _)  = GT

instance (HOrdHet (Sing (f r)), HOrdHet (Sing (g r))) => HOrdHet (Sing ((:+:) f g r)) where
  hcompareIx (TInl x) (TInl x') = hcompareIx x x'
  hcompareIx (TInl _) (TInr _)  = HLT
  hcompareIx (TInr y) (TInr y') = hcompareIx y y'
  hcompareIx (TInr _) (TInl _)  = HGT

-- | Logic variable.
data LVar (f :: (* -> *) -> (* -> *)) ix where
  LVar :: Integer -> Sing (f (Term f)) ix -> LVar f ix
  -- deriving (Show, Eq, Ord)

instance HEq (LVar h) where
  -- heq :: (Eq (Sing ix)) => LVar h ix -> LVar h ix -> Bool
  -- heq (LVar n x) (LVar m y) = n == m && (==) x y
  heq (LVar n _) (LVar m _) = n == m

instance (HEqHet (Sing (h (Term h)))) => HEqHet (LVar h) where
  heqIx (LVar _ x) (LVar _ y) =
    case heqIx x y of
      Just Refl -> Just Refl
      Nothing   -> Nothing

instance (HOrd (Sing (h (Term h)))) => HOrd (LVar h) where
  hcompare (LVar n x) (LVar m y) = compare n m <> hcompare x y

instance (HOrdHet (Sing (h (Term h)))) => HOrdHet (LVar h) where
  hcompareIx (LVar _ x) (LVar _ y) = hcompareIx x y

instance HShow (LVar f) where
  hshowsPrec n (LVar m _) = \xs -> showParen (n == 11) (\ys -> "LVar " ++ show m ++ ys) xs

-- suc :: LVar h ix -> LVar h ix
-- suc (LVar n x) = LVar (n + 1) x
--
-- suc' :: (HFunctor h) => LVar h ix -> h f ix' -> LVar h ix'
-- suc' (LVar n _) y = LVar (n + 1) $ hfmap (const $ K ()) y

mkLVar :: (SingI (h (Term h)) ix) => Integer -> LVar h ix
mkLVar n = LVar n sing

-- mkLVarType :: (TypeRep h) => Integer -> Type h ix -> LVar h ix
-- mkLVarType n t = LVar n t

newtype Subst h = Subst (HMap (LVar h) (Term h))

lookup :: (HOrdHet (Sing (h (Term h)))) => LVar h ix -> Subst h -> Maybe (Term h ix)
lookup k (Subst s) = HM.lookup k s

lookupVar :: Integer -> Subst h -> Maybe (Some (Term h))
lookupVar n (Subst s) = HM.lookupWith (\(LVar m _) -> compare n m) s

extend :: (HOrdHet (Sing (h (Term h)))) => LVar h ix -> Term h ix -> Subst h -> Subst h
extend k v (Subst s) = Subst $ HM.insert k v s

domain :: Subst h -> [Some (LVar h)]
domain (Subst s) = HM.keys s

empty :: Subst t
empty = Subst HM.empty


