{-# LANGUAGE FlexibleInstances #-}
module Language.DSKanren.Sugar where
import Language.DSKanren.Core

-- | Disjunction of many clauses. This can be thought as a logical
-- switch.
conde :: [Predicate] -> Predicate
conde = foldr disconj failure

-- | Conjuction of many clauses. Think of this as a sort of logical
-- semicolon.
program :: [Predicate] -> Predicate
program = foldr conj success

-- | Only grab n solutions. Useful for when the full logic program
-- might not terminate. Or takes its sweet time to do so.
runN :: Int -> (Term -> Predicate) -> [(Term, [Neq])]
runN n = take n . run

-- | We often want to introduce many fresh variables at once. We've
-- encoded this in DSKanren with the usual type class hackery for
-- variadic functions.
class MkFresh a where
  -- | Instantiate @a@ with as many fresh terms as needed to produce a
  -- predicate.
  manyFresh :: a -> Predicate
instance MkFresh a => MkFresh (Term -> a) where
  manyFresh = fresh . fmap manyFresh
instance MkFresh Predicate where
  manyFresh = id

list :: [Term] -> Term
list = foldr Pair (Atom "nil")

class IsTerm a where
  -- | Reify a normal haskell value to a logical value.
  term :: a -> Term
instance IsTerm Int where
  term = Integer . fromIntegral
instance IsTerm Integer where
  term = Integer
instance IsTerm a => IsTerm [a] where
  term = foldr Pair (Integer 0) . map term
