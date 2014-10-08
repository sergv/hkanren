-- | Test to ensure that unification function as intended.
module Main where
import Language.DSKanren
import Test.Tasty
import Test.Tasty.QuickCheck hiding ((===))
import QuickCheckHelper

reflexive :: TestTree
reflexive = testProperty "Reflexivity"
            . forAll (mkTerm [currentGoal])
            $ \t -> hasSolution (t === t)

commutative :: TestTree
commutative = testProperty "Commutative"
              . forAll (two $ mkTerm [currentGoal])
              $ \ (l, r) ->
                 hasSolution (l === r)
                 ==> hasSolution (r === l)

trans :: TestTree
trans = testProperty "Transitive"
        . forAll (three $ mkTerm [currentGoal])
        $ \(l, m, r) ->
               hasSolution (conj (l === m) (m === r))
           ==> hasSolution (r === l)

main :: IO ()
main = defaultMain . testGroup "List Tests" $
       [ reflexive
       , commutative
       , trans]
