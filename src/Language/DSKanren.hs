-- | DSKanren is a small implementation of the
-- <http://minikanren.org miniKanren> language. The toplevel
-- module exports the core language, in 'Language.DSKanren.Core'
--  and some simple combinators from 'Language.DSKanren.Sugar'.
--
-- The core API of miniKanren is
--
--   ['disconj']
--     Try the left and the right and gather solutions that satisfy
--     either one.
--   ['fresh']
--     Create a fresh logical variable
--   ['===']
--     Equate two terms. This will backtrack if we can't unify
--     them in this branch.
--   ['run']
--     Actually run a logical computation and return results and
--     the constraints on them.
--
--  In addition to these core combinators, we also export a few
--  supplimentary tools.
--
--    ['=/=']
--      The opposite of '===', ensure that the left and right
--      never unify.
--    ['suco']
--      A binary relationship where @n@ is related to @n + 1@.
--
-- We can define the classic @appendo@ relationship by encoding
-- lists in the Lisp "bunch-o-pairs" method.
--
-- @
--    appendo :: 'Term' -> 'Term' -> 'Term' -> 'Predicate'
--    appendo l r o =
--     'conde' [ 'program' [l '===' Integer 0,  o '===' r]
--           , 'manyFresh' $ \h t o' ->
--               'program' [ 'Pair' h t '===' l
--                       , appendo t r o'
--                       , 'Pair' h o' '===' o ]]
-- @
--
-- Once we have a relationship, we can run it backwards and forwards
-- as we can with most logic programs.
--
-- >>> runN 1 $ appendo (term [1, 2]) (term [3])
-- [(Pair (Integer 1) (Pair (Integer 2) (Pair (Integer 3) (Integer 0))), [])]
-- >>> runN 1 $ \t -> appendo t t (term [1, 1])
-- p(Pair (Integer 1) (Integer 0), [])]
-- >>> runN 1 $ runN 1 $ \t -> appendo t (term 0) t
-- [(Integer 0,[])]
--
module Language.DSKanren ( module Language.DSKanren.Core
                         , module Language.DSKanren.Sugar ) where
import Language.DSKanren.Core
import Language.DSKanren.Sugar

appendo :: Term -> Term -> Term -> Predicate
appendo l r o =
  conde [ program [l === Integer 0,  o === r]
        , manyFresh $ \h t o' ->
            program [ Pair h t === l
                    , appendo t r o'
                    , Pair h o' === o ]]
