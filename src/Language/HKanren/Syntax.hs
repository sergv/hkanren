{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes          #-}

module Language.HKanren.Syntax where

import Data.HOrdering
import Data.HUtils
import Data.List
import Language.HKanren.Core
import Language.HKanren.Subst (TypeI, Type)

-- | Disjunction of many clauses. This can be thought as a logical
-- switch.
conde :: (HFoldable h, Unifiable h h)
      => [Predicate h] -> Predicate h
conde = foldr disconj failure

-- | Conjuction of many clauses. Think of this as a sort of logical
-- semicolon.
program :: (HFoldable h, Unifiable h h)
        => [Predicate h] -> Predicate h
program = foldr conj success

-- | Only grab n solutions. Useful for when the full logic program
-- might not terminate. Or takes its sweet time to do so.
runN :: forall h ix. (HFunctorId h, HFoldable h, Unifiable h h, TypeI (h (Term h)) ix, HOrdHet (Type (h (Term h))))
     => Integer -> (Term h ix -> Predicate h) -> [(Some (Term h), [Some (Neq h)])]
runN n = genericTake n . run

-- -- | We often want to introduce many fresh variables at once. We've
-- -- encoded this in DSKanren with the usual type class hackery for
-- -- variadic functions.
-- class MkFresh a where
--   -- | Instantiate @a@ with as many fresh terms as needed to produce a
--   -- predicate.
--   manyFresh :: a -> Predicate h
--
-- instance MkFresh a => MkFresh (Term -> a) where
--   manyFresh = fresh . fmap manyFresh
--
-- instance MkFresh Predicate where
--   manyFresh = id

-- -- | Build a lispish list out of terms. The atom @"nil"@ will serve as
-- -- the empty list and 'Pair' will be ':'.
-- list :: [Term] -> Term
-- list = foldr Pair (Atom "nil")
