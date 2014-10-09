{-# LANGUAGE RecordWildCards #-}
module Language.DSKanren.Core ( Term(..)
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
                              , run ) where
import           Control.Monad.Logic
import           Data.String
import qualified Data.Map            as M

-- | The abstract type of variables. As a consumer you should never
-- feel the urge to manipulate these directly.
newtype Var = V Integer deriving (Eq, Ord)

instance Show Var where
  show (V i) = '_' : show i

suc :: Var -> Var
suc (V i) = V (i + 1)

-- | The terms of our logical language.
data Term = Var Var        -- ^ Logical variables that can unify with
                           -- other terms
          | Atom String    -- ^ The equivalent of Scheme's symbols or
                           -- keywords
          | Pair Term Term -- ^ Pairs of terms
          deriving Eq

instance Show Term where
  show t = case t of
    Var v -> show v
    Atom a -> '\'' : a
    Pair l r -> "(" ++ show l ++ ", " ++ show r ++ ")"

instance IsString Term where
  fromString = Atom

type Sol = M.Map Var Term

-- | Substitute all bound variables in a term giving the canonical
-- term in an environment. Sometimes the solution isn't canonical,
-- so some ugly recursion happens. Happily we don't have to prove
-- normalization.
canonize :: Sol -> Term -> Term
canonize sol t = case t of
  Atom a -> Atom a
  Pair l r -> canonize sol l `Pair` canonize sol r
  Var i -> maybe (Var i) (canonize $ M.delete i sol) $ M.lookup i sol

-- | Ensures that a variable doesn't occur in some other term. This
-- prevents us from getting some crazy infinite term. None of that
-- nonsense.
notIn :: Var -> Term -> Bool
notIn v t = case t of
  Var v' -> v /= v'
  Atom _ -> True
  Pair l r -> notIn v l && notIn v r

-- | Extend an environment with a given term. Note that
-- that we don't even bother to canonize things here, that
-- can wait until we extact a solution.
extend :: Var -> Term -> Sol -> Sol
extend = M.insert

-- | Unification cannot need not backtrack so this will either
-- universally succeed or failure. Tricksy bit, we don't want to allow
-- infinite terms since that can be narly. To preserve reflexivity, we
-- have a special check for when we compare a var to itself. This
-- doesn't extend the enviroment. With this special case we can add a
-- check to make sure we never unify a var with a term containing it.
unify :: Term -> Term -> Sol -> Maybe Sol
unify l r sol= case (l, r) of
  (Atom a, Atom a') | a == a' -> Just sol
  (Pair h t, Pair h' t') -> unify h h' sol >>= unify t t'
  (Var i, Var j) | i == j -> Just sol
  (Var i, t) | i `notIn` t -> Just (extend i t sol)
  (t, Var i) | i `notIn` t -> Just (extend i t sol)
  _ -> Nothing

type Neq = (Term, Term)
data State = State { sol :: Sol
                   , var :: Var
                   , neq :: [Neq] }
newtype Predicate = Predicate {unPred :: State -> Logic State}

-- | Validate the inqualities still hold.
-- To do this we try to unify each pair under the current
-- solution, if this fails we're okay. If they *don't* then
-- make sure that the solution under which they unify is an
-- extension of the solution set, ie we must add more facts
-- to get a contradiction.
checkNeqs :: State -> Logic State
checkNeqs s@State{..} = foldr go (return s) neq
  where go (l, r) m =
          case unify (canonize sol l) (canonize sol r) sol of
           Nothing -> m
           Just badSol -> if domain badSol == domain sol then mzero else m
        domain = M.keys

-- | Equating two terms will attempt to unify them and backtrack if
-- this is impossible.
(===) :: Term -> Term -> Predicate
(===) l r = Predicate $ \s@State {..} ->
  case unify (canonize sol l) (canonize sol r) sol of
   Just sol' -> checkNeqs s{sol = sol'}
   Nothing   -> mzero

-- | The opposite of unification. If any future unification would
-- cause these two terms to become equal we'll backtrack.
(=/=) :: Term -> Term -> Predicate
(=/=) l r = Predicate $ \s@State{..} -> checkNeqs s{neq = (l, r) : neq}

-- | Generate a fresh (not rigid) term to use for our program.
fresh :: (Term -> Predicate) -> Predicate
fresh withTerm =
  Predicate $ \State{..} ->
               unPred (withTerm $ Var var) $ State sol (suc var) neq

-- | Conjunction. This will return solutions that satsify both the
-- first and second predicate.
conj :: Predicate -> Predicate -> Predicate
conj p1 p2 = Predicate $ \s -> unPred p1 s >>- unPred p2

-- | Disjunction. This will return solutions that satisfy either the
-- first predicate or the second.
disconj :: Predicate -> Predicate -> Predicate
disconj p1 p2 = Predicate $ \s -> unPred p1 s `interleave` unPred p2 s

-- | The Eeyore of predicates, always fails. This is mostly useful as
-- a way of pruning out various conditions, as in
-- @'conj' (a '===' b) 'failure'@. This is also an identity for
-- 'disconj'.
failure :: Predicate
failure = Predicate $ const mzero

-- | The Tigger of predicates! always passes. This isn't very useful
-- on it's own, but is helpful when building up new combinators. This
-- is also an identity for 'conj'.
success :: Predicate
success = Predicate return

-- | The goal that this logic program is trying to create. This is
-- occasionally useful when we're doing generating programs.
currentGoal :: Term
currentGoal = Var (V 0)

-- | Run a program and find all solutions for the parametrized term.
run :: (Term -> Predicate) -> [(Term, [Neq])]
run mkProg = map answer . observeAll $ prog
  where prog = unPred (fresh mkProg) (State M.empty (V 0) [])
        answer State{..} = (canonize sol . Var $ V 0, neq)
