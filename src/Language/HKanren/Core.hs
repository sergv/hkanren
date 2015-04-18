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
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.HKanren.Core
  ( Term
  , LVar
  , Neq
  , (===)
  , (===*)
  , (=/=)
  , fresh
  , conj
  , disconj
  , Predicate
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

import Data.HOrdering
import Data.HUtils

import Language.HKanren.Subst (Subst, Term, TypeI(..), LVar, mkLVar)
import qualified Language.HKanren.Subst as S

class Unifiable (h :: (* -> *) -> (* -> *)) (g :: (* -> *) -> (* -> *)) where
  unify :: h (Term g) ix -> h (Term g) ix -> Subst g -> Maybe (Subst g)

instance (Unifiable f g, Unifiable f' g) => Unifiable (f :+: f') g where
  unify (Inl x) (Inl y) = unify x y
  unify (Inr x) (Inr y) = unify x y
  unify _       _       = const Nothing

unifyTerms
  :: (HFoldable h, Unifiable h h, HOrdHet (Type (h (Term h))))
  => HFree h (LVar h) ix -> HFree h (LVar h) ix -> Subst h -> Maybe (Subst h)
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
  :: forall h ix. (HFoldable h, HOrdHet (Type (h (Term h))))
  => LVar h ix -> HFree h (LVar h) ix -> Bool
occursCheck var = getAny . go
  where
    go :: HFree h (LVar h) ix' -> Any
    go (HPure var') = Any $ var ==* var'
    go (HFree h)    = hfoldMap go h


-- | Substitute all bound variables in a term giving the canonical
-- term in an environment. Sometimes the solution isn't canonical,
-- so some ugly recursion happens. Happily we don't have to prove
-- normalization.
canonize :: forall h ix. (HFunctorId h, HOrdHet (Type (h (Term h)))) => Subst h -> Term h ix -> Term h ix
canonize subst = go Set.empty
  where
    go :: Set (Some (LVar h)) -> Term h ix' -> Term h ix'
    go usedVars t =
      case t of
        HPure v
          | Set.member v' usedVars -> t
          | otherwise              ->
            maybe t (go usedVars') $ S.lookup v subst
          where
            usedVars' = Set.insert v' usedVars
            v'        = Some v
        HFree x -> HFree $ hfmapId (go usedVars) x

-- | Represents inequalities. @(l, r)@ means that @l@ will not unify
-- with @r@ within the current environment.
data Neq h ix = Neq (Term h ix) (Term h ix)

data State h = State
  { subst      :: Subst h
  , freeVarIdx :: Integer
  , neq        :: [Some (Neq h)]
  }

newtype Predicate h = Predicate { unPred :: State h -> Logic (State h) }

-- | Validate the inqualities still hold.
-- To do this we try to unify each pair under the current
-- solution, if this fails we're okay. If they *don't* then
-- make sure that the solution under which they unify is an
-- extension of the solution set, ie we must add more facts
-- to get a contradiction.
checkNeqs :: forall h. (HFunctorId h, HFoldable h, Unifiable h h, HOrdHet (Type (h (Term h)))) => State h -> Logic (State h)
checkNeqs s@State{..} = foldr go (return s) neq
  where
    go :: Some (Neq h) -> Logic (State h) -> Logic (State h)
    go (Some (Neq l r)) m =
      case unifyTerms (canonize subst l) (canonize subst r) subst of
        Nothing -> m
        Just badSubst
          | S.domain badSubst == S.domain subst -> mzero
          | otherwise                           -> m

-- | Equating two terms will attempt to unify them and backtrack if
-- this is impossible.
(===) :: (HFunctorId h, HFoldable h, Unifiable h h, HOrdHet (Type (h (Term h))))
      => Term h ix -> Term h ix -> Predicate h
(===) l r = Predicate $ \s@State {..} ->
  case unifyTerms (canonize subst l) (canonize subst r) subst of
    Just subst' -> checkNeqs s { subst = subst' }
    Nothing     -> mzero

(===*) :: (HFunctorId h, HFoldable h, Unifiable h h, HEqHet (h (Term h)), HOrdHet (Type (h (Term h))))
       => Term h ix -> Term h ix' -> Predicate h
(===*) l r =
  case heqIx l r of
    Just Refl -> l === r
    Nothing   -> Predicate $ \_ -> mzero

-- | The opposite of unification. If any future unification would
-- cause these two terms to become equal we'll backtrack.
(=/=) :: (HFunctorId h, HFoldable h, Unifiable h h, HOrdHet (Type (h (Term h))))
      => Term h ix -> Term h ix -> Predicate h
(=/=) l r = Predicate $ \s@State{..} -> checkNeqs s { neq = Some (Neq l r) : neq }

-- | Generate a fresh (not rigid) term to use for our program.
fresh :: (HFoldable h, Unifiable h h, TypeI (h (Term h)) ix)
      => (Term h ix -> Predicate h) -> Predicate h
fresh withTerm = Predicate $
  \s@(State{freeVarIdx}) ->
    unPred (withTerm $ HPure $ mkLVar freeVarIdx) $ s { freeVarIdx = freeVarIdx + 1 }

-- | Conjunction. This will return solutions that satsify both the
-- first and second predicate.
conj :: (HFoldable h, Unifiable h h)
     => Predicate h -> Predicate h -> Predicate h
conj p1 p2 = Predicate $ \s -> unPred p1 s >>- unPred p2

-- | Disjunction. This will return solutions that satisfy either the
-- first predicate or the second.
disconj :: (HFoldable h, Unifiable h h)
        => Predicate h -> Predicate h -> Predicate h
disconj p1 p2 = Predicate $ \s -> unPred p1 s `interleave` unPred p2 s

-- | The always failing predicate. This is mostly useful as
-- a way of pruning out various conditions, as in
-- @'conj' (a '===' b) 'failure'@. This is also an identity for
-- 'disconj'.
failure :: Predicate h
failure = Predicate $ const mzero

-- | The always passing predicate. This isn't very useful
-- on it's own, but is helpful when building up new combinators. This
-- is also an identity for 'conj'.
success :: Predicate h
success = Predicate return

-- | Run a program and find all solutions for the parametrized term.
run :: forall h ix. (HFunctorId h, HFoldable h, Unifiable h h, TypeI (h (Term h)) ix, HOrdHet (Type (h (Term h))))
    => (Term h ix -> Predicate h) -> [(Some (Term h), [Some (Neq h)])]
run mkProg = catMaybes $ map answer $ observeAll prog
  where
    initVar = 0
    prog = unPred (fresh mkProg) (State S.empty initVar [])
    answer :: State h -> Maybe (Some (Term h), [Some (Neq h)])
    answer State{subst, neq} =
      case S.lookupVar initVar subst of
        Just (Some t) -> Just (Some $ canonize subst t, neq)
        Nothing       -> Nothing
