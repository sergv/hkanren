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
  )
where

import Data.HMap (HMap)
import qualified Data.HMap as HM
import Data.HOrdering
import Data.HUtils
import Data.Monoid
import Data.Type.Equality

import Prelude hiding (lookup)

type ClosedTerm h = HFix h
-- type Type t = ClosedTerm (TypeOf t)
type Term h = HFree h (LVar (ClosedTerm h))


class SingI (a :: * -> *) (ix :: *) where
  data Sing a :: * -> *
  sing :: Sing a ix

class SingOpt (a :: * -> *) (ix :: *) where
  singOpt :: Maybe (Sing a ix)

instance (SingI (f (HFix f ix)) ix) => SingI (HFix f ix) ix where
  data Sing (HFix f ix) ix where
    THFix :: Sing f ix -> Sing (HFix f ix) ix
  sing = THFix sing

instance (SingI (f (HFix f ix)) ix) => SingI (HFree f a ix) ix where
  data Sing (HFree f a ix) ix where
    THFree :: Sing f ix -> Sing (HFree f a ix) ix
  sing = THFree sing

instance (SingOpt f ix, SingI g ix) => SingI ((:+:) f g r) ix where
  data Sing ((:+:) f g r) ix where
    TInl :: Sing f ix -> Sing ((:+:) f g r) ix
    TInr :: Sing g ix -> Sing ((:+:) f g r) ix
  sing =
    case singOpt :: Maybe (Sing f ix) of
      Just x  -> TInl x
      Nothing -> TInr sing

instance (SingOpt f ix, SingI g ix) => SingOpt ((:+:) f g r) ix where
  singOpt =
    case singOpt :: Maybe (Sing f ix) of
      Just x  -> Just $ TInl x
      Nothing -> Just $ TInr sing

-- singOf :: (SingI h ix) => p ix -> Sing h ix
-- singOf _ = sing

-- cannot define these
-- instance HEq Sing where
--   heq a b = _
--
-- instance HEqHet Sing where
--
-- instance HOrd Sing where
--
-- instance HOrdHet Sing where

-- instance (SingI (f :: (* -> *) -> (* -> *)), SingI (g :: (* -> *) -> (* -> *))) => SingI (f :+: g) where
--   data Sing (f :+: g) where
--     TInl :: Sing f -> Sing (f :+: g)
--     TInr :: Sing g -> Sing (f :+: g)
--   sing = foo


-- | Logic variable.
data LVar (f :: * -> *) ix where
  LVar :: Integer -> Sing f ix -> LVar f ix
  -- deriving (Show, Eq, Ord)


instance HEq (LVar h) where
  -- heq :: (Eq (Sing ix)) => LVar h ix -> LVar h ix -> Bool
  -- heq (LVar n x) (LVar m y) = n == m && (==) x y
  heq (LVar n _) (LVar m _) = n == m

instance (HEqHet (Sing h)) => HEqHet (LVar h) where
  heqIx (LVar _ x) (LVar _ y) =
    case heqIx x y of
      Just Refl -> Just Refl
      Nothing   -> Nothing

instance (HOrd (Sing h)) => HOrd (LVar h) where
  hcompare (LVar n x) (LVar m y) = compare n m <> hcompare x y

instance (HOrdHet (Sing h)) => HOrdHet (LVar h) where
  hcompareIx (LVar _ x) (LVar _ y) = hcompareIx x y

instance HShow (LVar f) where
  hshowsPrec n (LVar m _) = \xs -> showParen (n == 11) (\ys -> "LVar " ++ show m ++ ys) xs

-- suc :: LVar h ix -> LVar h ix
-- suc (LVar n x) = LVar (n + 1) x
--
-- suc' :: (HFunctor h) => LVar h ix -> h f ix' -> LVar h ix'
-- suc' (LVar n _) y = LVar (n + 1) $ hfmap (const $ K ()) y

mkLVar :: (SingI h ix) => Integer -> LVar h ix
mkLVar n = LVar n sing

-- mkLVarType :: (TypeRep h) => Integer -> Type h ix -> LVar h ix
-- mkLVarType n t = LVar n t

newtype Subst h = Subst (HMap (LVar (ClosedTerm h)) (Term h))

lookup :: (HEqHet (Sing h), HOrdHet (Sing h)) => LVar h ix -> Subst h -> Maybe (Term h ix)
lookup k (Subst s) = HM.lookup k s

lookupVar :: Integer -> Subst h -> Maybe (Some (Term h))
lookupVar n (Subst s) = HM.lookupWith (\(LVar m _) -> compare n m) s

extend :: (HEqHet (Sing h), HOrdHet (Sing h)) => LVar h ix -> Term h ix -> Subst h -> Subst h
extend k v (Subst s) = Subst $ HM.insert k v s

domain :: Subst h -> [Some (LVar h)]
domain (Subst s) = HM.keys s

empty :: Subst t
empty = Subst HM.empty


