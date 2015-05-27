{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.HKanren.Syntax
  ( conde
  , condp
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

import Control.Arrow
import Control.Monad.AbstractLogic (AbstractLogic)
import Data.HOrdering
import Data.HUtils
import Data.Proxy (Proxy)
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
  => AbstractLogic m n
  => Proxy m
  -> Int
  -> (Term k ix -> Predicate k)
  -> n [(Term k ix, [Some (Neq k)])]
runN nondetProxy n f = Core.runN n (toPrimPredicate nondetProxy . f)

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
  => AbstractLogic m n
  => Proxy m
  -> (Term k ix -> Predicate k)
  -> n [(Term k ix, [Some (Neq k)])]
run nondetProxy f = Core.run (toPrimPredicate nondetProxy . f)

toPrimPredicate
  :: forall k m n.
     Unifiable (LFunctor k) k
  => HFoldable (LFunctor k)
  => HFunctorId (LFunctor k)
  => HOrdHet (Type (Term1 k))
  => HOrdHet (Term1 k)
  => HShow (Term1 k)
  => HPretty (Term1 k)
  => Ord (LDomain k)
  => Show (LDomain k)
  => LVar k
  => AbstractLogic m n
  => Proxy m
  -> Predicate k
  -> PrimPredicate m k
toPrimPredicate _ = go
  where
    go :: Predicate k -> PrimPredicate m k
    go Success                   = Core.success
    go Failure                   = Core.failure
    go (Combine Conjunction x y) = Core.conj (go x) (go y)
    go (Combine Disjunction x y) = Core.disconj (go x) (go y)
    go (ProbabilisticDisj cases) = Core.probabilisticDisconj (map (second go) cases)
    go (WithFresh f)             = Core.fresh (go . f)
    go (x :=== y)                = x Core.=== y
    go (x :===* y)               = x Core.===* y
    go (x :=/= y)                = x Core.=/= y
    go (CanonizeDbg t f)         = Core.canonizeDbg t (go . f)

data CombType = Conjunction | Disjunction
  deriving (Show, Eq, Ord, Enum, Bounded)

data Predicate k where
  Success           :: Predicate k
  Failure           :: Predicate k
  Combine           :: CombType -> Predicate k -> Predicate k -> Predicate k
  ProbabilisticDisj :: [(Int, Predicate k)] -> Predicate k
  WithFresh         :: (TypeI (Term1 k) ix) => (Term k ix -> Predicate k) -> Predicate k
  (:===)            :: (TypeI (Term1 k) ix) => Term k ix  -> Term k ix -> Predicate k
  (:=/=)            :: Term k ix -> Term k ix -> Predicate k
  -- this operator is very fishy
  (:===*)           :: Term k ix -> Term k ix' -> Predicate k
  CanonizeDbg       :: Term k ix -> (PP.Doc -> Predicate k) -> Predicate k

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

probabilisticDisj :: [(Int, Predicate k)] -> Predicate k
probabilisticDisj = ProbabilisticDisj

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
  condeImpl xs = foldr1 disj $ reverse xs

instance (Conde a, CondeVar a ~ k) => Conde (Predicate k -> a) where
  type CondeVar (Predicate k -> a) = k
  condeImpl xs x = condeImpl (x : xs)

conde :: (Conde a) => a
conde = condeImpl []


class ProbabilistictConde a where
  type ProbabilisticCondeVar a :: (* -> *)
  probabilisticCondeImpl :: [(Int, Predicate (ProbabilisticCondeVar a))] -> a

instance ProbabilistictConde (Predicate k) where
  type ProbabilisticCondeVar (Predicate k) = k
  probabilisticCondeImpl = probabilisticDisj . reverse

instance (ProbabilistictConde a, ProbabilisticCondeVar a ~ k) => ProbabilistictConde ((Int, Predicate k) -> a) where
  type ProbabilisticCondeVar ((Int, Predicate k) -> a) = k
  probabilisticCondeImpl xs x = probabilisticCondeImpl (x : xs)

condp :: (ProbabilistictConde a) => a
condp = probabilisticCondeImpl []

