-- | Test to ensure that unification function as intended.
module Main where
import Language.DSKanren
import Test.Tasty
import Test.Tasty.QuickCheck hiding ((===))
import QuickCheckHelper

--------------------------- Equal -------------------------------------
eqrefl :: TestTree
eqrefl = testProperty "Reflexivity"
            . forTerm
            $ \t -> hasSolution (t === t)

eqcomm :: TestTree
eqcomm = testProperty "Commutative"
         . forTerm2
         $ \ l r ->
            hasSolution (l === r)
            ==> hasSolution (r === l)

eqtrans :: TestTree
eqtrans = testProperty "Transitive"
          . forTerm3
          $ \l m r ->
             hasSolution (conj (l === m) (m === r))
             ==> hasSolution (r === l)

eqTests :: TestTree
eqTests = testGroup "Equality" [eqrefl, eqcomm, eqtrans]

--------------------------- Fresh ------------------------------------
freshClosed :: TestTree
freshClosed = testProperty "Closed Under Fresh"
              . forPred
              $ \p -> hasSolution p ==> hasSolution (fresh $ const p)
freshUnify :: TestTree
freshUnify = testProperty "Unification Under Fresh"
             . forTerm
             $ \t -> forPred $ \p ->
             hasSolution p
             ==> hasSolution . fresh $ \v -> conj (t === v) p

freshTests :: TestTree
freshTests = testGroup "Fresh" [freshClosed, freshUnify]

--------------------------- Conj -------------------------------------
conjid :: TestTree
conjid = testProperty "Commutative"
              . forPred
              $ \p -> hasSolution p ==> hasSolution (conj success p)

conjcomm :: TestTree
conjcomm = testProperty "Commutative"
              . forPred2
              $ \p o ->
                 hasSolution (conj p o) ==> hasSolution (conj o p)

conjassoc :: TestTree
conjassoc = testProperty "Associative"
            . forPred3
            $ \l m r ->
               hasSolution (conj (conj l m) r)
               ==> hasSolution (conj l (conj m r))

conjTests :: TestTree
conjTests = testGroup "Conj" [conjid, conjcomm, conjassoc]

------------------------- Disconj ------------------------------------
disconjid :: TestTree
disconjid = testProperty "Commutative"
            . forPred
            $ \p -> hasSolution p ==> hasSolution (disconj failure p)

disconjcomm :: TestTree
disconjcomm = testProperty "Commutative"
              . forPred2
              $ \p o ->
                 hasSolution (disconj p o) ==> hasSolution (disconj o p)

disconjassoc :: TestTree
disconjassoc = testProperty "Associative"
               . forPred3
               $ \l m r ->
                  hasSolution (disconj (disconj l m) r)
                  ==> hasSolution (disconj l (disconj m r))

disconjTests :: TestTree
disconjTests = testGroup "Disconj" [disconjid, disconjcomm, disconjassoc]

------------------------- Success --------------------------------------
annihilatorDisconj :: TestTree
annihilatorDisconj = testProperty "Annihilates Disconj"
                     . forPred
                     $ \p -> hasSolution (disconj success p)

successTests :: TestTree
successTests = testGroup "Success" [annihilatorDisconj]

------------------------ Failure ---------------------------------------
annihilatorConj :: TestTree
annihilatorConj = testProperty "Annihilates Disconj"
                     . forPred
                     $ \p -> not $ hasSolution (conj failure p)

failureTests :: TestTree
failureTests = testGroup "Success" [annihilatorConj]

main :: IO ()
main = defaultMain . testGroup "List Tests" $
       [ eqTests
       , freshTests
       , conjTests
       , disconjTests
       , successTests
       , failureTests ]
