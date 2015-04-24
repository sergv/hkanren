{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.HKanren.Core
  ( Term
  , Term1
  , LFunctor
  , LVar
  , LDomain
  , Neq
  , (===)
  , (===*)
  , (=/=)
  , fresh
  , conj
  , disconj
  , PrimPredicate
  , failure
  , success
  , run
  , Unifiable(..)
  , unifyTerms
  )
where

import Control.Monad.Logic
import Data.Maybe
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Type.Equality
import qualified Text.PrettyPrint.Leijen.Text as PP

import Data.HOrdering
import Data.HUtils

import Language.HKanren.Subst (Subst, LDomain, Term, Term1, LFunctor, TypeI(..), LVar, mkLVar)
import qualified Language.HKanren.Subst as S

-- import Debug.Trace

class Unifiable (h :: (* -> *) -> (* -> *)) k where
  unify :: h (Term k) ix -> h (Term k) ix -> Subst k -> Maybe (Subst k)

instance (Unifiable f k, Unifiable f' k) => Unifiable (f :+: f') k where
  -- {-# INLINABLE unify #-}
  unify (Inl x) (Inl y) = unify x y
  unify (Inr x) (Inr y) = unify x y
  unify _       _       = const Nothing

unifyTerms
  :: (HFoldable (LFunctor k), Unifiable (LFunctor k) k, HOrdHet (Type (Term1 k)), LVar k)
  => Term k ix -> Term k ix -> Subst k -> Maybe (Subst k)
unifyTerms (HPure x) y'@(HPure y) s
  | heq x y   = Just s
  | otherwise = Just $ S.extend x y' s
unifyTerms (HPure x) y s
  | occursCheck x y = Nothing
  | otherwise       = Just $ S.extend x y s
unifyTerms x (HPure y) s
  | occursCheck y x = Nothing
  | otherwise       = Just $ S.extend y x s
unifyTerms (HFree h) (HFree h') s = unify h h' s

-- | Check whether given logical variable appears inside another term.
occursCheck
  :: forall k ix. (HFoldable (LFunctor k), HOrdHet (Type (Term1 k)), LVar k)
  => k ix -> Term k ix -> Bool
occursCheck var = getAny . go
  where
    go :: Term k ix' -> Any
    go (HPure var') = Any $ var ==* var'
    go (HFree h)    = hfoldMap go h


-- | Substitute all bound variables in a term giving the canonical
-- term in an environment. Sometimes the solution isn't canonical,
-- so some ugly recursion happens. Happily we don't have to prove
-- normalization.
canonize
  :: forall k ix. (HFunctorId (LFunctor k), HOrdHet (Type (Term1 k)), Ord (LDomain k), LVar k)
  => Subst k -> Term k ix -> Term k ix
canonize subst = go Set.empty
  where
    go :: Set (LDomain k) -> Term k ix' -> Term k ix'
    go usedVars t =
      case t of
        HPure v
          | Set.member v' usedVars -> t
          | otherwise              ->
            maybe t (go usedVars') $ S.lookup v subst
          where
            usedVars' = Set.insert v' usedVars
            v'        = S.getDomain v
        HFree x -> HFree $ hfmapId (go usedVars) x

-- | Represents inequalities. @(l, r)@ means that @l@ will not unify
-- with @r@ within the current environment.
data Neq k ix = Neq (Term k ix) (Term k ix)

instance (HShow (Term h)) => HShow (Neq h) where
  hshowsPrec n (Neq x y) =
    showParen (n == 11) (showString "Neq " . hshowsPrec 11 x . showString " " . hshowsPrec 11 y)

instance (HPretty (Term h)) => HPretty (Neq h) where
  hpretty (Neq x y) = hpretty x PP.<+> "=/=" PP.<+> hpretty y

data State k = State
  { subst      :: Subst k
  , freeVarIdx :: Integer
  , neq        :: [Some (Neq k)]
  }

newtype PrimPredicate k = PrimPredicate { unPred :: State k -> Logic (State k) }

-- | Validate the inqualities still hold.
-- To do this we try to unify each pair under the current
-- solution, if this fails we're okay. If they *don't* then
-- make sure that the solution under which they unify is an
-- extension of the solution set, ie we must add more facts
-- to get a contradiction.
checkNeqs
  :: forall k.
     HFunctorId (LFunctor k)
  => HFoldable (LFunctor k)
  => Unifiable (LFunctor k) k
  => HOrdHet (Type (Term1 k))
  => LVar k
  => Ord (LDomain k)
  => State k
  -> Logic (State k)
checkNeqs s@State{..} = foldr go (return s) neq
  where
    substSize = S.domainSize subst
    substDomain = S.domain subst
    go :: Some (Neq k) -> Logic (State k) -> Logic (State k)
    go (Some (Neq l r)) m =
      case unifyTerms (canonize subst l) (canonize subst r) subst of
        Nothing -> m
        Just badSubst
          | S.domainSize badSubst == substSize && S.domain badSubst == substDomain -> mzero
          -- unification never removes anything from the substitution, so comparing
          -- domains is redundant here
          --- | S.domain badSubst == substDomain -> mzero
          | otherwise                           -> m

-- | Equating two terms will attempt to unify them and backtrack if
-- this is impossible.
(===)
  :: HFunctorId (LFunctor k)
  => HFoldable (LFunctor k)
  => Unifiable (LFunctor k) k
  => HOrdHet (Type (Term1 k))
  => HShow (Term1 k)
  => Ord (LDomain k)
  => LVar k
  => Term k ix
  -> Term k ix
  -> PrimPredicate k
(===) l r = PrimPredicate $ \s@State {..} ->
  case unifyTerms (canonize subst l) (canonize subst r) subst of
    Just subst' -> checkNeqs (s { subst = subst' })
    Nothing     -> mzero

(===*)
  :: HFunctorId (LFunctor k)
  => HFoldable (LFunctor k)
  => Unifiable (LFunctor k) k
  => HEqHet (Term1 k)
  => HOrdHet (Type (Term1 k))
  => HShow (Term1 k)
  => Ord (LDomain k)
  => LVar k
  => Term k ix
  -> Term k ix'
  -> PrimPredicate k
(===*) l r =
  case heqIx l r of
    Just Refl -> l === r
    Nothing   -> PrimPredicate $ \_ -> mzero

-- | The opposite of unification. If any future unification would
-- cause these two terms to become equal we'll backtrack.
(=/=)
  :: HFunctorId (LFunctor k)
  => HFoldable (LFunctor k)
  => Unifiable (LFunctor k) k
  => HOrdHet (Type (Term1 k))
  => Ord (LDomain k)
  => LVar k
  => Term k ix
  -> Term k ix
  -> PrimPredicate k
(=/=) l r = PrimPredicate $ \s@State{..} -> checkNeqs s { neq = Some (Neq l r) : neq }

-- | Generate a fresh (not rigid) term to use for our program.
fresh :: (HFoldable (LFunctor k), Unifiable (LFunctor k) k, TypeI (Term1 k) ix, LVar k)
      => (Term k ix -> PrimPredicate k) -> PrimPredicate k
fresh withTerm = PrimPredicate $
  \s@(State{freeVarIdx}) ->
    -- trace ("fresh variable " ++ show freeVarIdx ++ ", # neqs = " ++ show (length $ neq s)) $
    unPred (withTerm $ HPure $ mkLVar freeVarIdx) $ s { freeVarIdx = freeVarIdx + 1 }

-- | Conjunction. This will return solutions that satsify both the
-- first and second predicate.
conj :: (HFoldable (LFunctor k), Unifiable (LFunctor k) k)
     => PrimPredicate k -> PrimPredicate k -> PrimPredicate k
conj p1 p2 = PrimPredicate $ \s -> unPred p1 s >>- unPred p2

-- | Disjunction. This will return solutions that satisfy either the
-- first predicate or the second.
disconj :: (HFoldable (LFunctor k), Unifiable (LFunctor k) k)
        => PrimPredicate k -> PrimPredicate k -> PrimPredicate k
disconj p1 p2 = PrimPredicate $ \s ->
  unPred p1 s `interleave` unPred p2 s

-- | The always failing predicate. This is mostly useful as
-- a way of pruning out various conditions, as in
-- @'conj' (a '===' b) 'failure'@. This is also an identity for
-- 'disconj'.
failure :: PrimPredicate k
failure = PrimPredicate $ const mzero

-- | The always passing predicate. This isn't very useful
-- on it's own, but is helpful when building up new combinators. This
-- is also an identity for 'conj'.
success :: PrimPredicate k
success = PrimPredicate return

-- | Run a program and find all solutions for the parametrized term.
run ::
  forall k ix.
     HFunctorId (LFunctor k)
  => HFoldable (LFunctor k)
  => Unifiable (LFunctor k) k
  => TypeI (Term1 k) ix
  => HOrdHet (Type (Term1 k))
  => HShow (Term1 k)
  => Ord (LDomain k)
  => LVar k
  => (Term k ix -> PrimPredicate k)
  -> [(Term k ix, [Some (Neq k)])]
run mkProg = catMaybes $ map answer $ observeAll prog
  where
    initVarIdx = 0
    initVar :: k ix
    initVar = mkLVar initVarIdx
    prog = unPred (fresh mkProg) (State S.empty initVarIdx [])
    answer :: State k -> Maybe (Term k ix, [Some (Neq k)])
    answer State{subst, neq} =
      case S.lookup initVar subst of
        Just t  -> Just (canonize subst t, neq)
        Nothing -> Nothing
