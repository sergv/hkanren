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
