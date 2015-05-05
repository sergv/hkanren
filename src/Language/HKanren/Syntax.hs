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
  , (>>)
  , (>>=)
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
  , (=/^)
  , (^/=)
  , (^/^)
  , canonizeDbg

  , fresh
  , V(..)

  , Predicate

  , LVar
  , TypeI
  , Unifiable
  , Term
  , Term1
  , LFunctor
  , LDomain
  , Type
  , Neq
  )
where

import Data.HOrdering
import Data.HUtils
import Language.HKanren.Core (PrimPredicate, Unifiable, Term, Term1, LFunctor, Neq, LVar, LDomain)
import qualified Language.HKanren.Core as Core
import Language.HKanren.Subst (TypeI, Type)
import qualified Text.PrettyPrint.Leijen.Text as PP

import Prelude hiding ((>>), (>>=))

-- | Only grab n solutions. Useful for when the full logic program
-- might not terminate. Or takes its sweet time to do so.
runN
  :: Unifiable (LFunctor k) k
  => HFoldable (LFunctor k)
  => HFunctorId (LFunctor k)
  => HOrdHet (Type (Term1 k))
  => HOrdHet (Term1 k)
  => HShow (Term1 k)
  => HPretty (Term1 k)
  => TypeI (Term1 k) ix
  => Ord (LDomain k)
  => Show (LDomain k)
  => LVar k
  => Int
  -> (Term k ix -> Predicate k)
  -> [(Term k ix, [Some (Neq k)])]
runN n f = Core.runN n (toPrimPredicate . f)

run
  :: Unifiable (LFunctor k) k
  => HFoldable (LFunctor k)
  => HFunctorId (LFunctor k)
  => HOrdHet (Type (Term1 k))
  => HOrdHet (Term1 k)
  => HShow (Term1 k)
  => HPretty (Term1 k)
  => TypeI (Term1 k) ix
  => Ord (LDomain k)
  => Show (LDomain k)
  => LVar k
  => (Term k ix -> Predicate k)
  -> [(Term k ix, [Some (Neq k)])]
run f = Core.run (toPrimPredicate . f)

toPrimPredicate
  :: Unifiable (LFunctor k) k
  => HFoldable (LFunctor k)
  => HFunctorId (LFunctor k)
  => HOrdHet (Type (Term1 k))
  => HOrdHet (Term1 k)
  => HShow (Term1 k)
  => HPretty (Term1 k)
  => Ord (LDomain k)
  => Show (LDomain k)
  => LVar k
  => Predicate k
  -> PrimPredicate k
toPrimPredicate Success                   = Core.success
toPrimPredicate Failure                   = Core.failure
toPrimPredicate (Combine Conjunction x y) = Core.conj (toPrimPredicate x) (toPrimPredicate y)
toPrimPredicate (Combine Disjunction x y) = Core.disconj (toPrimPredicate x) (toPrimPredicate y)
toPrimPredicate (WithFresh f)             = Core.fresh (toPrimPredicate . f)
toPrimPredicate (x :=== y)                = x Core.=== y
toPrimPredicate (x :===* y)               = x Core.===* y
toPrimPredicate (x :=/= y)                = x Core.=/= y
toPrimPredicate (CanonizeDbg t f)         = Core.canonizeDbg t (toPrimPredicate . f)


data CombType = Conjunction | Disjunction
  deriving (Show, Eq, Ord, Enum, Bounded)

data Predicate k where
  Success   :: Predicate k
  Failure   :: Predicate k
  Combine   :: CombType -> Predicate k -> Predicate k -> Predicate k
  WithFresh :: (TypeI (Term1 k) ix) => (Term k ix -> Predicate k) -> Predicate k
  (:===)    :: (TypeI (Term1 k) ix) => Term k ix  -> Term k ix -> Predicate k
  (:=/=)    :: Term k ix -> Term k ix -> Predicate k
  -- this operator is very fishy
  (:===*)   :: Term k ix -> Term k ix' -> Predicate k
  CanonizeDbg :: Term k ix -> (PP.Doc -> Predicate k) -> Predicate k

(===) :: (TypeI (Term1 k) ix) => Term k ix -> Term k ix -> Predicate k
(===) = (:===)

(===*) :: Term k ix -> Term k ix' -> Predicate k
(===*) = (:===*)

(=/=) :: Term k ix -> Term k ix -> Predicate k
(=/=) = (:=/=)

(=/^) :: (f :<: LFunctor k) => Term k ix -> f (Term k) ix -> Predicate k
(=/^) x y = x =/= inject y

(^/=) :: (f :<: LFunctor k) => f (Term k) ix -> Term k ix -> Predicate k
(^/=) x y = inject x =/= y

(^/^) :: (f :<: LFunctor k) => f (Term k) ix -> f (Term k) ix -> Predicate k
(^/^) x y = inject x =/= inject y

(^==) :: (TypeI (Term1 k) ix, f :<: LFunctor k)
      => f (Term k) ix -> Term k ix -> Predicate k
(^==) l r = inject l === r

(==^) :: (TypeI (Term1 k) ix, f :<: LFunctor k)
      => Term k ix -> f (Term k) ix -> Predicate k
(==^) l r = l === inject r

(^=^) :: (TypeI (Term1 k) ix, f :<: LFunctor k)
      => f (Term k) ix -> f (Term k) ix -> Predicate k
(^=^) l r = inject l === inject r


success :: Predicate k
success = Success

failure :: Predicate k
failure = Failure

conj :: Predicate k -> Predicate k -> Predicate k
conj = Combine Conjunction

disj :: Predicate k -> Predicate k -> Predicate k
disj = Combine Disjunction

canonizeDbg :: Term k ix -> (PP.Doc -> Predicate k) -> Predicate k
canonizeDbg = CanonizeDbg

-- | We often want to introduce many fresh variables at once. We've
-- encoded this in DSKanren with the usual type class hackery for
-- variadic functions.
class MkFresh a where
  type MkFreshVar a :: (* -> *)
  -- | Instantiate @a@ with as many fresh terms as needed to produce a
  -- predicate.
  fresh :: a -> Predicate (MkFreshVar a)

-- ^ V for Variable. Wrapper for MkFresh
newtype V k ix = V { unT :: Term k ix }

instance (MkFresh a, MkFreshVar a ~ k, TypeI (Term1 k) ix, f ~ LFunctor k) => MkFresh (HFree f k ix -> a) where
  type MkFreshVar (HFree f k ix -> a) = k
  fresh f = WithFresh $ fresh . f

instance MkFresh (Predicate k) where
  type MkFreshVar (Predicate k) = k
  fresh = id


(>>) :: Predicate k -> Predicate k -> Predicate k
(>>) = conj

(>>=)
  :: (TypeI (Term1 k) ix)
  => (Term k ix -> Predicate k)
  -> (Term k ix -> Predicate k)
  -> Predicate k
(>>=) f g = fresh $ \x -> conj (f x) (g x)

class Conde a where
  type CondeVar a :: (* -> *)
  condeImpl :: [Predicate (CondeVar a)] -> a

instance Conde (Predicate k) where
  type CondeVar (Predicate k) = k
  condeImpl [] = Failure
  condeImpl xs = foldr1 (Combine Disjunction) $ reverse xs

instance (Conde a, CondeVar a ~ k) => Conde (Predicate k -> a) where
  type CondeVar (Predicate k -> a) = k
  condeImpl xs x = condeImpl (x : xs)

conde :: (Conde a) => a
conde = condeImpl []
