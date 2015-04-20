{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.HKanren.Syntax
  ( conde
  , conj
  , disj
  , fresh
  , Fresh(..)
  , success
  , failure
  , run
  , runN
  , (===)
  , (==^)
  , (^==)
  , (^=^)
  , (===*)
  , (=/=)

  , manyFresh

  , Predicate
  )
where

import Data.HOrdering
import Data.HUtils
import Data.List
import Language.HKanren.Core (PrimPredicate, Unifiable, Term, Neq)
import qualified Language.HKanren.Core as Core
import Language.HKanren.Subst (TypeI, Type)

-- | Only grab n solutions. Useful for when the full logic program
-- might not terminate. Or takes its sweet time to do so.
runN
  :: Unifiable h h
  => HFoldable h
  => HFunctorId h
  => HOrdHet (Type (h (Term h)))
  => HOrdHet (h (Term h))
  => HShow (h (Term h))
  => TypeI (h (Term h)) ix
  => Integer
  -> (Term h ix -> Predicate h)
  -> [(Term h ix, [Some (Neq h)])]
runN n = genericTake n . run

run
  :: Unifiable h h
  => HFoldable h
  => HFunctorId h
  => HOrdHet (Type (h (Term h)))
  => HOrdHet (h (Term h))
  => HShow (h (Term h))
  => TypeI (h (Term h)) ix
  => (Term h ix -> Predicate h)
  -> [(Term h ix, [Some (Neq h)])]
run f = Core.run (toPrimPredicate . f)

toPrimPredicate
  :: Unifiable h h
  => HFoldable h
  => HFunctorId h
  => HOrdHet (Type (h (Term h)))
  => HOrdHet (h (Term h))
  => HShow (h (Term h))
  => Predicate h
  -> PrimPredicate h
toPrimPredicate Success                   = Core.success
toPrimPredicate Failure                   = Core.failure
toPrimPredicate (Combine Conjunction x y) = Core.conj (toPrimPredicate x) (toPrimPredicate y)
toPrimPredicate (Combine Disjunction x y) = Core.disconj (toPrimPredicate x) (toPrimPredicate y)
toPrimPredicate (WithFresh f)             = Core.fresh (toPrimPredicate . f)
toPrimPredicate (x :=== y)                = x Core.=== y
toPrimPredicate (x :===* y)               = x Core.===* y
toPrimPredicate (x :=/= y)                = x Core.=/= y


-- | We often want to introduce many fresh variables at once. We've
-- encoded this in DSKanren with the usual type class hackery for
-- variadic functions.
class MkFresh a where
  type MkFreshFunctor a :: (* -> *) -> (* -> *)
  -- | Instantiate @a@ with as many fresh terms as needed to produce a
  -- predicate.
  manyFresh :: a -> Predicate (MkFreshFunctor a)

instance (MkFresh a, MkFreshFunctor a ~ h, TypeI (h (Term h)) ix) => MkFresh (Term h ix -> a) where
  type MkFreshFunctor (Term h ix -> a) = h
  manyFresh = WithFresh . fmap manyFresh

instance MkFresh (Predicate h) where
  type MkFreshFunctor (Predicate h) = h
  manyFresh = id


data CombType = Conjunction | Disjunction
  deriving (Show, Eq, Ord, Enum, Bounded)

-- data SCombType (c :: CombType) where
--   SConjunction :: SCombType Conjunction
--   SDisjunction :: SCombType Disjunction

data Predicate h where
  Success   :: Predicate h
  Failure   :: Predicate h
  Combine   :: CombType -> Predicate h -> Predicate h -> Predicate h
  WithFresh :: (TypeI (h (Term h)) ix) => (Term h ix -> Predicate h) -> Predicate h
  (:===)    :: (TypeI (h (Term h)) ix) => Term h ix  -> Term h ix -> Predicate h
  (:=/=)    :: Term h ix -> Term h ix -> Predicate h
 -- this operator is very fishy
  (:===*)   :: Term h ix -> Term h ix' -> Predicate h

(===) :: (TypeI (h (Term h)) ix) => Term h ix -> Term h ix -> Predicate h
(===) = (:===)

(===*) :: Term h ix -> Term h ix' -> Predicate h
(===*) = (:===*)

(=/=) :: Term h ix -> Term h ix -> Predicate h
(=/=) = (:=/=)

(^==) :: (TypeI (h (Term h)) ix, f :<: h)
      => f (Term h) ix -> Term h ix -> Predicate h
(^==) l r =  inject l === r

(==^) :: (TypeI (h (Term h)) ix, f :<: h)
      => Term h ix -> f (Term h) ix -> Predicate h
(==^) l r =  l === inject r

(^=^) :: (TypeI (h (Term h)) ix, f :<: h)
      => f (Term h) ix -> f (Term h) ix -> Predicate h
(^=^) l r =  inject l === inject r


success :: Predicate h
success = Success

failure :: Predicate h
failure = Failure

conj :: Predicate h -> Predicate h -> Predicate h
conj = Combine Conjunction

disj :: Predicate h -> Predicate h -> Predicate h
disj = Combine Disjunction


data Fresh ix = Fresh

fresh :: (TypeI (h (Term h)) ix) => Fresh ix -> (Term h ix -> Predicate h) -> Predicate h
fresh Fresh = WithFresh


class Conde a where
  type CondeFunctor a :: (* -> *) -> (* -> *)
  -- | Instantiate @a@ with as many fresh terms as needed to produce a
  -- predicate.
  -- disj :: a
  condeImpl :: [Predicate (CondeFunctor a)] -> a

instance Conde (Predicate h) where
  type CondeFunctor (Predicate h) = h
  -- disj = Core.failure
  condeImpl [] = Failure
  condeImpl xs = foldr1 (Combine Disjunction) $ reverse xs

instance (Conde a, CondeFunctor a ~ h) => Conde (Predicate h -> a) where
  type CondeFunctor (Predicate h -> a) = h
  -- disj pred = Core.disconj pred (disj :: a)
  condeImpl xs x = condeImpl (x : xs)

conde :: (Conde a) => a
conde = condeImpl []
