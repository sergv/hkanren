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
                              , suco
                              , zero
                              , failure
                              , success
                              , run ) where
import           Control.Monad.Logic
import           Data.String
import qualified Data.Map            as M

-- | The abstract type of variables. As a consumer you should never
-- feel the urge to manipulate these directly.
newtype Var = V {unVar :: Integer} deriving (Eq, Ord)

instance Show Var where
  show (V i) = '_' : show i

suc :: Var -> Var
suc (V i) = V (i + 1)

-- | The terms of our logical language.
data Term = Var Var         -- ^ Logical variables that can unify with other terms
          | Atom String     -- ^ The equivalent of Scheme's symbols or keywords
          | Integer Integer -- ^ Boring old numbers
          | Pair Term Term  -- ^ Pairs of terms

instance Show Term where
  show t = case t of
    Var v -> show v
    Atom a -> a
    Integer i -> show i
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
  Integer i -> Integer i
  Pair l r -> canonize sol l `Pair` canonize sol r
  Var i -> maybe (Var i) (canonize $ M.delete i sol) $ M.lookup i sol

-- | Extend an environment with a given term. Note that
-- that we don't even bother to canonize things here, that
-- can wait until we extact a solution.
extend :: Var -> Term -> Sol -> Sol
extend = M.insert

-- | Unification cannot need not backtrack so this will either
-- universally succeed or failure.
unify :: Term -> Term -> Sol -> Maybe Sol
unify l r sol= case (l, r) of
  (Atom a, Atom a') | a == a' -> Just sol
  (Integer i, Integer j) | i == j -> Just sol
  (Pair h t, Pair h' t') -> unify h h' sol >>= unify t t'
  (Var i, t) -> Just (extend i t sol)
  (t, Var i) -> Just (extend i t sol)
  _ -> Nothing

type Neq = (Term, Term)
data State = State { sol :: Sol
                   , var :: Var
                   , neq :: [Neq] }
newtype Predicate = Predicate {unPred :: State -> Logic State}

-- | Validate the inqualities still hold
checkNeqs :: State -> Logic State
checkNeqs s@State{..} = foldr go (return s) neq
  where go (l, r) m =
          case unify (canonize sol l) (canonize sol r) sol of
           Nothing -> m
           Just _  -> mzero

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
(=/=) l r = Predicate $ \s@State{..} -> return s{neq = (l, r) : neq}

-- | Generate a fresh (not rigid) term to use for our program.
fresh :: (Term -> Predicate) -> Predicate
fresh withTerm =
  Predicate $ \State{..} ->
               unPred (withTerm $ Var var) $ State sol (suc var) neq

-- | Successor, only unify l and r if l is r + 1
suco :: Term -> Term -> Predicate
suco l r = Predicate $ \ s@State{..} -> case (canonize sol l, canonize sol r) of
  (Integer i, _) -> unPred (r === Integer (i + 1)) s
  (_, Integer i) -> unPred (l === Integer (i - 1)) s
  _ -> mzero

zero :: Term -> Predicate
zero = (=== Integer 0)

-- | Conjunction
conj :: Predicate -> Predicate -> Predicate
conj p1 p2 = Predicate $ \s -> unPred p1 s >>- unPred p2

-- | Disjunction
disconj :: Predicate -> Predicate -> Predicate
disconj p1 p2 = Predicate $ \s -> unPred p1 s `interleave` unPred p2 s

-- | The Eeyore of predicates, always fails.
failure :: Predicate
failure = Predicate $ const mzero

-- | The tigger of predicates! always passes.
success :: Predicate
success = Predicate return

-- | Run a program and find all solutions for the parametrized term.
run :: (Term -> Predicate) -> [(Term, [Neq])]
run mkProg = map answer . observeAll $ prog >>= checkNeqs
  where prog = unPred (fresh mkProg) (State M.empty (V 0) [])
        answer State{..} = (canonize sol . Var $ V 0, neq)
