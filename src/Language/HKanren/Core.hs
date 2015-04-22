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
  , LVar
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
  => Term h ix -> Term h ix -> Subst h -> Maybe (Subst h)
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
canonize
  :: forall h ix. (HFunctorId h, HOrdHet (Type (h (Term h))))
  => Subst h -> Term h ix -> Term h ix
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

instance (HShow (Term h)) => HShow (Neq h) where
  hshowsPrec n (Neq x y) = \xs -> showParen (n == 11) (showString "Neq " . hshowsPrec 11 x . showString " " . hshowsPrec 11 y) xs

instance (HPretty (Term h)) => HPretty (Neq h) where
  hpretty (Neq x y) = hpretty x PP.<+> "=/=" PP.<+> hpretty y

data State h = State
  { subst      :: Subst h
  , freeVarIdx :: Integer
  , neq        :: [Some (Neq h)]
  }

newtype PrimPredicate h = PrimPredicate { unPred :: State h -> Logic (State h) }

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
(===) :: (HFunctorId h, HFoldable h, Unifiable h h, HOrdHet (Type (h (Term h))), HShow (h (Term h)))
      => Term h ix -> Term h ix -> PrimPredicate h
(===) l r = PrimPredicate $ \s@State {..} ->
  case unifyTerms (canonize subst l) (canonize subst r) subst of
    Just subst' -> checkNeqs (s { subst = subst' })
    Nothing     -> mzero

(===*) :: (HFunctorId h, HFoldable h, Unifiable h h, HEqHet (h (Term h)), HOrdHet (Type (h (Term h))), HShow (h (Term h)))
       => Term h ix -> Term h ix' -> PrimPredicate h
(===*) l r =
  case heqIx l r of
    Just Refl -> l === r
    Nothing   -> PrimPredicate $ \_ -> mzero

-- | The opposite of unification. If any future unification would
-- cause these two terms to become equal we'll backtrack.
(=/=) :: (HFunctorId h, HFoldable h, Unifiable h h, HOrdHet (Type (h (Term h))))
      => Term h ix -> Term h ix -> PrimPredicate h
(=/=) l r = PrimPredicate $ \s@State{..} -> checkNeqs s { neq = Some (Neq l r) : neq }

-- | Generate a fresh (not rigid) term to use for our program.
fresh :: (HFoldable h, Unifiable h h, TypeI (h (Term h)) ix)
      => (Term h ix -> PrimPredicate h) -> PrimPredicate h
fresh withTerm = PrimPredicate $
  \s@(State{freeVarIdx}) ->
    unPred (withTerm $ HPure $ mkLVar freeVarIdx) $ s { freeVarIdx = freeVarIdx + 1 }

-- | Conjunction. This will return solutions that satsify both the
-- first and second predicate.
conj :: (HFoldable h, Unifiable h h)
     => PrimPredicate h -> PrimPredicate h -> PrimPredicate h
conj p1 p2 = PrimPredicate $ \s -> unPred p1 s >>- unPred p2

-- | Disjunction. This will return solutions that satisfy either the
-- first predicate or the second.
disconj :: (HFoldable h, Unifiable h h)
        => PrimPredicate h -> PrimPredicate h -> PrimPredicate h
disconj p1 p2 = PrimPredicate $ \s ->
  unPred p1 s `interleave` unPred p2 s

-- | The always failing predicate. This is mostly useful as
-- a way of pruning out various conditions, as in
-- @'conj' (a '===' b) 'failure'@. This is also an identity for
-- 'disconj'.
failure :: PrimPredicate h
failure = PrimPredicate $ const mzero

-- | The always passing predicate. This isn't very useful
-- on it's own, but is helpful when building up new combinators. This
-- is also an identity for 'conj'.
success :: PrimPredicate h
success = PrimPredicate return

-- | Run a program and find all solutions for the parametrized term.
run :: forall h ix. (HFunctorId h, HFoldable h, Unifiable h h, TypeI (h (Term h)) ix, HOrdHet (Type (h (Term h))), HShow (h (Term h)))
    => (Term h ix -> PrimPredicate h) -> [(Term h ix, [Some (Neq h)])]
run mkProg = catMaybes $ map answer $ observeAll prog
  where
    initVarIdx = 0
    initVar :: LVar h ix
    initVar = mkLVar initVarIdx
    prog = unPred (fresh mkProg) (State S.empty initVarIdx [])
    answer :: State h -> Maybe (Term h ix, [Some (Neq h)])
    answer State{subst, neq} =
      case S.lookup initVar subst of
        Just t  -> Just (canonize subst t, neq)
        Nothing -> Nothing
