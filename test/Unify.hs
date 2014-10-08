-- | Test to ensure that unification function as intended.
module Main where
import Control.Applicative
import Language.DSKanren
import Test.Tasty
import Test.Tasty.QuickCheck hiding ((===))
import QuickCheckHelper

eqrefl :: TestTree
eqrefl = testProperty "Reflexivity"
            . forAll (mkTerm [currentGoal])
            $ \t -> hasSolution (t === t)

eqcomm :: TestTree
eqcomm = testProperty "Commutative"
         . forAll (two $ mkTerm [currentGoal])
         $ \ (l, r) ->
            hasSolution (l === r)
            ==> hasSolution (r === l)

eqtrans :: TestTree
eqtrans = testProperty "Transitive"
          . forAll (three $ mkTerm [currentGoal])
          $ \(l, m, r) ->
             hasSolution (conj (l === m) (m === r))
             ==> hasSolution (r === l)

eqTests :: TestTree
eqTests = testGroup "Equality" [eqrefl, eqcomm, eqtrans]

freshClosed :: TestTree
freshClosed = testProperty "Closed Under Fresh"
              . forAll (Blind <$> mkPred [currentGoal])
              $ \(Blind p) ->
                 hasSolution p ==> hasSolution (fresh $ const p)

freshTests :: TestTree
freshTests = testGroup "Fresh" [freshClosed]

conjid :: TestTree
conjid = testProperty "Commutative"
              . forAll (Blind <$> mkPred [currentGoal])
              $ \(Blind p) ->
                 hasSolution p ==> hasSolution (conj success p)
conjcomm :: TestTree
conjcomm = testProperty "Commutative"
              . forAll (two $ Blind <$> mkPred [currentGoal])
              $ \(Blind p, Blind o) ->
                 hasSolution (conj p o)
                 ==> hasSolution (conj p o)

conjTests :: TestTree
conjTests = testGroup "Conj" [conjid, conjcomm]

main :: IO ()
main = defaultMain . testGroup "List Tests" $
       [ eqTests
       , freshTests
       , conjTests]
