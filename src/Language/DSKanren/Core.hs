{-# LANGUAGE RecordWildCards #-}

module Language.DSKanren.Core
  ( Term(..)
  , Var
  , Neq
  , (===)
  , (=/=)
  , fresh
  , conj
  , disconj
  , Predicate
  , failure
  , success
  , currentGoal
  , run
  )
where

import Control.Monad.Logic
import Data.String

import Language.DSKanren.Subst (Subst, Var, suc, initV)
import qualified Language.DSKanren.Subst as S


-- | The terms of our logical language.
data Term =
    Var Var        -- ^ Logical variables that can unify with other terms
  | Atom String    -- ^ The equivalent of Scheme's symbols or keywords
  | Pair Term Term -- ^ Pairs of terms
  deriving (Eq, Ord)

instance Show Term where
  show t = case t of
    Var v    -> show v
    Atom a   -> '\'' : a
    Pair l r -> "(" ++ show l ++ ", " ++ show r ++ ")"

instance IsString Term where
  fromString = Atom


-- | Substitute all bound variables in a term giving the canonical
-- term in an environment. Sometimes the solution isn't canonical,
-- so some ugly recursion happens. Happily we don't have to prove
-- normalization.
canonize :: Subst Term -> Term -> Term
canonize subst t = case t of
  Atom a   -> t
  Pair l r -> canonize subst l `Pair` canonize subst r
  Var v    -> maybe t (canonize $ S.delete v subst) $ S.lookup v subst

-- | Occurs check.
--
-- Ensures that a variable doesn't occur in some other term. This
-- prevents us from getting some crazy infinite term. None of that
-- nonsense.
notIn :: Var -> Term -> Bool
notIn v t = case t of
  Var v'   -> v /= v'
  Atom _   -> True
  Pair l r -> notIn v l && notIn v r

-- | Unification cannot need not backtrack so this will either
-- universally succeed or failure. Tricksy bit, we don't want to allow
-- infinite terms since that can be narly. To preserve reflexivity, we
-- have a special check for when we compare a var to itself. This
-- doesn't extend the enviroment. With this special case we can add a
-- check to make sure we never unify a var with a term containing it.
unify :: Term -> Term -> Subst Term -> Maybe (Subst Term)
unify l r subst = go l r
  where
    go (Atom a) (Atom a')
      | a == a'                = Just subst
    go (Pair h t) (Pair h' t') = unify h h' subst >>= unify t t'
    go (Var v) (Var v')
      | v == v'                = Just subst
    go (Var v) t
      | v `notIn` t            = Just (S.extend v t subst)
    go t (Var v)
      | v `notIn` t            = Just (S.extend v t subst)
    go _  _                    = Nothing

-- | Represents inequalities. @(l, r)@ means that @l@ will not unify
-- with @r@ within the current environment.
type Neq = (Term, Term)

data State = State
  { subst :: Subst Term
  , var   :: Var
  , neq   :: [Neq]
  }

newtype Predicate = Predicate { unPred :: State -> Logic State }

-- | Validate the inqualities still hold.
-- To do this we try to unify each pair under the current
-- solution, if this fails we're okay. If they *don't* then
-- make sure that the solution under which they unify is an
-- extension of the solution set, ie we must add more facts
-- to get a contradiction.
checkNeqs :: State -> Logic State
checkNeqs s@State{..} = foldr go (return s) neq
  where
    go :: Neq -> Logic State -> Logic State
    go (l, r) m =
      case unify (canonize subst l) (canonize subst r) subst of
        Nothing -> m
        Just badSubst
          | S.domain badSubst == S.domain subst -> mzero
          | otherwise                           -> m

-- | Equating two terms will attempt to unify them and backtrack if
-- this is impossible.
(===) :: Term -> Term -> Predicate
(===) l r = Predicate $ \s@State {..} ->
  case unify (canonize subst l) (canonize subst r) subst of
    Just subst' -> checkNeqs s { subst = subst' }
    Nothing   -> mzero

-- | The opposite of unification. If any future unification would
-- cause these two terms to become equal we'll backtrack.
(=/=) :: Term -> Term -> Predicate
(=/=) l r = Predicate $ \s@State{..} -> checkNeqs s { neq = (l, r) : neq }

-- | Generate a fresh (not rigid) term to use for our program.
fresh :: (Term -> Predicate) -> Predicate
fresh withTerm = Predicate $
  \State{..} ->
    unPred (withTerm $ Var var) $ State subst (suc var) neq

-- | Conjunction. This will return solutions that satsify both the
-- first and second predicate.
conj :: Predicate -> Predicate -> Predicate
conj p1 p2 = Predicate $ \s -> unPred p1 s >>- unPred p2

-- | Disjunction. This will return solutions that satisfy either the
-- first predicate or the second.
disconj :: Predicate -> Predicate -> Predicate
disconj p1 p2 = Predicate $ \s -> unPred p1 s `interleave` unPred p2 s

-- | The always failing predicate. This is mostly useful as
-- a way of pruning out various conditions, as in
-- @'conj' (a '===' b) 'failure'@. This is also an identity for
-- 'disconj'.
failure :: Predicate
failure = Predicate $ const mzero

-- | The always passing predicate. This isn't very useful
-- on it's own, but is helpful when building up new combinators. This
-- is also an identity for 'conj'.
success :: Predicate
success = Predicate return

-- | The goal that this logic program is trying to create. This is
-- occasionally useful when we're doing generating programs.
currentGoal :: Term
currentGoal = Var initV

-- | Run a program and find all solutions for the parametrized term.
run :: (Term -> Predicate) -> [(Term, [Neq])]
run mkProg = map answer $ observeAll prog
  where
    prog = unPred (fresh mkProg) (State S.empty initV [])
    answer State{..} = (canonize subst $ Var initV, neq)
