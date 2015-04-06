----------------------------------------------------------------------------
-- |
-- Module      :  Language.HKanren.Playground
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.HKanren.Playground where

import Control.Monad
import Data.Monoid
import Data.Type.Equality

import Data.HMap (HMap)
import qualified Data.HMap as HM
import Data.HOrdering
import Data.HUtils

import Language.HKanren.Core

-- traverse :: (Applicative f) => (a -> f b) -> t a -> f (t b)

-- instance HEq

-- newtype Name = Name Int

-- data ExprF f ix where
--   Var  :: Name -> f Expr
--   Add  :: f Expr -> f Expr -> f Expr
--   Decl :: Name -> f Stmt
--   Set  :: Name -> f Expr -> f Stmt

data Name

data NameF (f :: * -> *) ix where
  Name :: Integer -> NameF f Name

-- instance HEq (NameF f) where
--   heq (Name n) (Name m) = n == m
--
-- instance HEqIx (NameF f) where
--   heqIx (Name _) (Name _) = Just Refl

instance HFunctor NameF where
  hfmap _ (Name n) = Name n

instance HFoldable NameF where
  hfoldMap _ _ = mempty

instance HTraversable NameF where
  htraverse _ (Name n) = pure $ Name n

data Expr

data VarF (f :: * -> *) ix where
  Var :: f Name -> VarF f Expr

instance HFunctor VarF where
  hfmap f (Var name) = Var $ f name

instance HFoldable VarF where
  hfoldMap f (Var name) = f name

data AddF (f :: * -> *) ix where
  Add :: f Expr -> f Expr -> AddF f Expr

instance HFunctor AddF where
  hfmap f (Add x y) = Add (f x) (f y)

instance HFoldable AddF where
  hfoldMap f (Add x y) = f x <> f y

data Stmt

data SetF (f :: * -> *) ix where
  Set :: f Name -> f Expr -> SetF f Stmt

instance HFunctor SetF where
  hfmap f (Set name expr) = Set (f name) (f expr)

instance HFoldable SetF where
  hfoldMap f (Set name expr) = f name <> f expr

data List ix

data ListF (f :: * -> *) ix where
  Nil  :: ListF f (List ix)
  Cons :: f ix -> ListF f ix -> ListF f (List ix)

instance HFunctor ListF where
  hfmap _ Nil         = Nil
  hfmap f (Cons x xs) = Cons (f x) (hfmap f xs)

instance HFoldable ListF where
  hfoldMap _ Nil         = mempty
  hfoldMap f (Cons x xs) = f x <> hfoldMap f xs

data Function

data FunctionF (f :: * -> *) ix where
  Function :: f Name -> f (List Name) -> f (List Stmt) -> f Expr -> FunctionF f Function

instance HFunctor FunctionF where
  hfmap f (Function name args body ret) =
    Function (f name) (f args) (f body) (f ret)

instance HFoldable FunctionF where
  hfoldMap f (Function name args body ret) =
    f name <> f args <> f body <> f ret


type ProgF = FunctionF :+: SetF :+: VarF :+: AddF :+: ListF :+: NameF
type Prog = HFix ProgF


type ProgWithVars = HFree ProgF (LVar ProgF)


instance Unifiable NameF g where
  unify (Name n) (Name m) s
    | n == m    = Just s
    | otherwise = Nothing

instance (HFoldable g, Unifiable g g, HOrdIx (g HUnit)) => Unifiable ListF g where
  unify Nil         Nil         = Just
  unify (Cons x xs) (Cons y ys) = unifyTerms x y >=> unify xs ys
  unify _           _           = const Nothing

instance (HFoldable g, Unifiable g g, HOrdIx (g HUnit)) => Unifiable VarF g where
  unify (Var x) (Var y) s = unifyTerms x y s

-- | It is crucial to bind unifications into one another so that updated
-- substitutions get propagated!
instance (HFoldable g, Unifiable g g, HOrdIx (g HUnit)) => Unifiable AddF g where
  unify (Add x y) (Add x' y') = unifyTerms x x' >=> unifyTerms y y'

instance (HFoldable g, Unifiable g g, HOrdIx (g HUnit)) => Unifiable SetF g where
  unify (Set name expr) (Set name' expr') =
    unifyTerms name name' >=> unifyTerms expr expr'

instance (HFoldable g, Unifiable g g, HOrdIx (g HUnit)) => Unifiable FunctionF g where
  unify (Function name args body ret) (Function name' args' body' ret') =
    unifyTerms name name' >=> unifyTerms args args' >=> unifyTerms body body' >=> unifyTerms ret ret'

-- Foldable + HZip is enough for unification. Just zip two functors
-- and fold over Klendo Maybe (Subst h) monoid.
-- This won't work as there would be no HZip instance for (:+:) - i.e.
-- what would it return for (hzip (Inl _) (Inr _))?

-- May need an HMap for substitutions to make sure that
-- variable with a given index ix is mapped to the term with the same index.
-- Since indices correspond to plain types, this linking is of crucial
-- importance!



-- unifyTerms :: HFree f LVar ix -> HFree f LVar ix -> Maybe (Map (LVar ix) (HFree f LVar ix))
-- unifyTerms = undefined

main :: IO ()
main = do
  undefined
