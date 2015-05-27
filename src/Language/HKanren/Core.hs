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
  , probabilisticDisconj
  , PrimPredicate
  , failure
  , success
  , run
  , runN
  , Unifiable(..)
  , unifyTerms
  , canonizeDbg
  )
where

import Control.Arrow
import Control.Monad.AbstractLogic (AbstractLogic)
import qualified Control.Monad.AbstractLogic as AL
import Data.Maybe
import Data.Monoid
import Data.Pointed
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

canonizeDbg
  :: (HFunctorId (LFunctor k), HOrdHet (Type (Term1 k)), Ord (LDomain k), LVar k, HPretty (Term1 k), AbstractLogic m n)
  => Term k ix -> (PP.Doc -> PrimPredicate m k) -> PrimPredicate m k
canonizeDbg t f = PrimPredicate $ \s@PredState{subst} ->
  unPred (f $ hpretty (canonize subst t)) s

-- | Represents inequalities. @(l, r)@ means that @l@ will not unify
-- with @r@ within the current environment.
data Neq k ix = Neq (Term k ix) (Term k ix)

instance (HShow (Term h)) => HShow (Neq h) where
  hshowsPrec n (Neq x y) =
    showParen (n == 11) (showString "Neq " . hshowsPrec 11 x . showString " " . hshowsPrec 11 y)

instance (HPretty (Term h)) => HPretty (Neq h) where
  hpretty (Neq x y) = hpretty x PP.<+> "=/=" PP.<+> hpretty y

data PredState k = PredState
  { subst      :: Subst k
  , freeVarIdx :: Integer
  , neq        :: [Some (Neq k)]
  }

-- m should be an instance of AbstractLogic
newtype PrimPredicate m k =
  PrimPredicate { unPred :: PredState k -> m (PredState k) }
-- ~=
-- StateT (PredState k) m ()
-- ~=
-- PredState k -> m ((), PredState k)
-- ~=
-- PredState k -> m (PredState k)
--
-- PredState k -> ContNondet c (PredState k)
-- ~=
-- PredState k -> (forall b. (PredState k -> c b) -> c b)
--
-- PredState k -> ContNondetT c (State RandState) (PredState k)
-- ~=
-- PredState k -> (forall b. (PredState k -> State RandState (c b)) -> State RandState (c b))
-- ~=
-- PredState k -> (forall b. (PredState k -> RandState -> (c b, RandState)) -> RandState -> (c b, RandState))

-- | Validate the inqualities still hold.
-- To do this we try to unify each pair under the current
-- solution, if this fails we're okay. If they *don't* then
-- make sure that the solution under which they unify is an
-- extension of the solution set, ie we must add more facts
-- to get a contradiction.
checkNeqs
  :: forall m n k.
     HFunctorId (LFunctor k)
  => HFoldable (LFunctor k)
  => Unifiable (LFunctor k) k
  => HOrdHet (Type (Term1 k))
  => HShow (Term1 k)
  => LVar k
  => Ord (LDomain k)
  => Show (LDomain k)
  => AbstractLogic m n
  => PredState k
  -> m (PredState k)
checkNeqs s@PredState{..} =
  foldr (\(Some n) -> checkNeq' n substSize substDomain s) (point s) neq
  where
    substSize   = S.domainSize subst
    substDomain = S.domain subst

checkNeq'
  :: forall k m n ix.
     HFunctorId (LFunctor k)
  => HFoldable (LFunctor k)
  => Unifiable (LFunctor k) k
  => HOrdHet (Type (Term1 k))
  => HShow (Term1 k)
  => LVar k
  => Ord (LDomain k)
  => Show (LDomain k)
  => AbstractLogic m n
  => Neq k ix
  -> LDomain k
  -> [LDomain k]
  -> PredState k
  -> m (PredState k)
  -> m (PredState k)
checkNeq' (Neq l r) substSize substDomain PredState{..} m =
  case unifyTerms (canonize subst l) (canonize subst r) subst of
    Nothing -> m
    Just badSubst
      | S.domainSize badSubst == substSize && S.domain badSubst == substDomain -> AL.failure
      -- unification never removes anything from the substitution, so comparing
      -- domains is redundant here
      --- | S.domain badSubst == substDomain -> mzero
      | otherwise -> m

checkNeq
  :: forall k m n ix.
     HFunctorId (LFunctor k)
  => HFoldable (LFunctor k)
  => Unifiable (LFunctor k) k
  => HOrdHet (Type (Term1 k))
  => HShow (Term1 k)
  => LVar k
  => Ord (LDomain k)
  => Show (LDomain k)
  => AbstractLogic m n
  => Neq k ix
  -> PredState k
  -> m (PredState k)
checkNeq n s@PredState{subst} =
  checkNeq' n substSize substDomain s (point s)
  where
    substSize   = S.domainSize subst
    substDomain = S.domain subst

-- | Equating two terms will attempt to unify them and backtrack if
-- this is impossible.
(===)
  :: HFunctorId (LFunctor k)
  => HFoldable (LFunctor k)
  => Unifiable (LFunctor k) k
  => HOrdHet (Type (Term1 k))
  => HShow (Term1 k)
  => HPretty (Term1 k)
  => Ord (LDomain k)
  => Show (LDomain k)
  => LVar k
  => AbstractLogic m n
  => Term k ix
  -> Term k ix
  -> PrimPredicate m k
(===) l r = PrimPredicate $ \s@PredState {..} ->
  case unifyTerms (canonize subst l) (canonize subst r) subst of
    Just subst' -> checkNeqs (s { subst = subst' })
    Nothing     -> AL.failure

(===*)
  :: HFunctorId (LFunctor k)
  => HFoldable (LFunctor k)
  => Unifiable (LFunctor k) k
  => HEqHet (Term1 k)
  => HOrdHet (Type (Term1 k))
  => HShow (Term1 k)
  => HPretty (Term1 k)
  => Ord (LDomain k)
  => Show (LDomain k)
  => LVar k
  => AbstractLogic m n
  => Term k ix
  -> Term k ix'
  -> PrimPredicate m k
(===*) l r =
  case heqIx l r of
    Just Refl -> l === r
    Nothing   -> PrimPredicate $ \_ -> AL.failure

-- | The opposite of unification. If any future unification would
-- cause these two terms to become equal we'll backtrack.
(=/=)
  :: HFunctorId (LFunctor k)
  => HFoldable (LFunctor k)
  => Unifiable (LFunctor k) k
  => HOrdHet (Type (Term1 k))
  => HShow (Term1 k)
  => Ord (LDomain k)
  => Show (LDomain k)
  => LVar k
  => AbstractLogic m n
  => Term k ix
  -> Term k ix
  -> PrimPredicate m k
(=/=) l r = PrimPredicate $ \s@PredState{..} ->
  let newNeq = Neq l r
  in  checkNeq newNeq (s { neq = Some newNeq : neq })

-- | Generate a fresh (not rigid) term to use for our program.
fresh :: (HFoldable (LFunctor k), Unifiable (LFunctor k) k, TypeI (Term1 k) ix, LVar k, AbstractLogic m n)
      => (Term k ix -> PrimPredicate m k) -> PrimPredicate m k
fresh withTerm = PrimPredicate $
  \s@(PredState{freeVarIdx}) ->
    unPred (withTerm $ HPure $ mkLVar freeVarIdx) $ s { freeVarIdx = freeVarIdx + 1 }

-- | Conjunction. This will return solutions that satsify both the
-- first and second predicate.
conj :: (HFoldable (LFunctor k), Unifiable (LFunctor k) k, AbstractLogic m n)
     => PrimPredicate m k -> PrimPredicate m k -> PrimPredicate m k
conj p1 p2 = PrimPredicate $ \s ->
  unPred p1 s AL.>>- unPred p2

-- | Disjunction. This will return solutions that satisfy either the
-- first predicate or the second.
disconj :: (HFoldable (LFunctor k), Unifiable (LFunctor k) k, AbstractLogic m n)
        => PrimPredicate m k -> PrimPredicate m k -> PrimPredicate m k
disconj p1 p2 = PrimPredicate $ \s ->
  unPred p1 s `AL.interleave` unPred p2 s

-- | Probabilistic disjunction.
probabilisticDisconj :: (HFoldable (LFunctor k), Unifiable (LFunctor k) k, AbstractLogic m n)
                 => [(Int, PrimPredicate m k)] -> PrimPredicate m k
probabilisticDisconj [] = failure
probabilisticDisconj cs = PrimPredicate $ \s ->
  AL.probabilisticChoice $ map (second (\p -> unPred p s)) cs


-- | The always failing predicate. This is mostly useful as
-- a way of pruning out various conditions, as in
-- @'conj' (a '===' b) 'failure'@. This is also an identity for
-- 'disconj'.
failure :: (AbstractLogic m n) => PrimPredicate m k
failure = PrimPredicate $ const AL.failure

-- | The always passing predicate. This isn't very useful
-- on it's own, but is helpful when building up new combinators. This
-- is also an identity for 'conj'.
success :: (AbstractLogic m n) => PrimPredicate m k
success = PrimPredicate point

-- | Run a program and find all solutions for the parametrized term.
run ::
  forall k m n ix.
     HFunctorId (LFunctor k)
  => HFoldable (LFunctor k)
  => Unifiable (LFunctor k) k
  => TypeI (Term1 k) ix
  => HOrdHet (Type (Term1 k))
  => HShow (Term1 k)
  => Ord (LDomain k)
  => LVar k
  => AbstractLogic m n
  => (Term k ix -> PrimPredicate m k)
  -> n [(Term k ix, [Some (Neq k)])]
run mkProg = fmap (catMaybes . map answer) $ AL.observeAll prog
  where
    initVarIdx = 0
    initVar :: k ix
    initVar = mkLVar initVarIdx
    prog = unPred (fresh mkProg) (PredState S.empty initVarIdx [])
    answer :: PredState k -> Maybe (Term k ix, [Some (Neq k)])
    answer PredState{subst, neq} =
      case S.lookup initVar subst of
        Just t  -> Just (canonize subst t, neq)
        Nothing -> Nothing

-- {-# INLINABLE run #-}
-- | Run a program and find first n solutions for the parametrized term.
runN ::
  forall k m n ix.
     HFunctorId (LFunctor k)
  => HFoldable (LFunctor k)
  => Unifiable (LFunctor k) k
  => TypeI (Term1 k) ix
  => HOrdHet (Type (Term1 k))
  => HShow (Term1 k)
  => Ord (LDomain k)
  => LVar k
  => AbstractLogic m n
  => Int
  -> (Term k ix -> PrimPredicate m k)
  -> n [(Term k ix, [Some (Neq k)])]
runN n mkProg = fmap (catMaybes . map answer) $ AL.observeMany n prog
  where
    initVarIdx = 0
    initVar :: k ix
    initVar = mkLVar initVarIdx
    prog = unPred (fresh mkProg) (PredState S.empty initVarIdx [])
    answer :: PredState k -> Maybe (Term k ix, [Some (Neq k)])
    answer PredState{subst, neq} =
      case S.lookup initVar subst of
        Just t  -> Just (canonize subst t, neq)
        Nothing -> Nothing

