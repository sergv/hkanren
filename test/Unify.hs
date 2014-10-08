-- | Test to ensure that unification function as intended.
module Main where
import Control.Applicative
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

closedFresh :: TestTree
closedFresh = testProperty "Closed Under Fresh"
              . forAll (Blind <$> mkPred [currentGoal])
              $ \(Blind p) ->
                 hasSolution p ==> hasSolution (fresh $ const p)

main :: IO ()
main = defaultMain . testGroup "List Tests" $
       [ reflexive
       , commutative
       , trans
       , closedFresh]
