-- | Test to ensure that unification function as intended.

{-# LANGUAGE ExistentialQuantification #-}

module Main where

import Data.HUtils
import Language.HKanren
import Test.Tasty
import Test.Tasty.QuickCheck hiding ((===))
import QuickCheckHelper

--------------------------- Equal -------------------------------------
eqrefl :: TestTree
eqrefl = testProperty "Reflexivity"
         . forTerm
         $ \(Some t) -> hasSolution (HFree t === HFree t)

eqcomm :: TestTree
eqcomm = testProperty "Commutative"
         . forTerm2
         $ \ (Some (l :*: r)) ->
            hasSolution (HFree l === HFree r)
            ==> hasSolution (HFree r === HFree l)

-- eqtrans :: TestTree
-- eqtrans = testProperty "Transitive"
--           . forTerm3
--           $ \l m r ->
--              hasSolution (conj (l === m) (m === r))
--              ==> hasSolution (r === l)

eqTests :: TestTree
eqTests = testGroup "Equality" [eqrefl, eqcomm] -- [, eqtrans]

------------------------ Not Equal -----------------------------------
neqarefl :: TestTree
neqarefl = testProperty "Antireflexive"
           . forTerm
           $ \(Some t) -> not $ hasSolution (HFree t =/= HFree t)

neqcomm :: TestTree
neqcomm = testProperty "Commutative"
          . forTerm2
          $ \(Some (l :*: r)) ->
             hasSolution (HFree l =/= HFree r)
             ==> hasSolution (HFree r =/= HFree l)

neqTests :: TestTree
neqTests = testGroup "Inequality" [neqarefl, neqcomm]


--------------------------- Fresh ------------------------------------
freshClosed :: TestTree
freshClosed = testProperty "Closed Under Fresh"
              . forPred
              $ \p -> hasSolution p ==> hasSolution (fresh templateAtom $ const p)

freshUnify :: TestTree
freshUnify = testProperty "Unification Under Fresh"
             . forTerm
             $ \(Some t) -> forPred $ \p ->
             hasSolution p
             ==> hasSolution . fresh t $ \v -> conj (HFree t === v) p

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

-- conjassoc :: TestTree
-- conjassoc = testProperty "Associative"
--             . forPred3
--             $ \l m r ->
--                hasSolution (conj (conj l m) r)
--                ==> hasSolution (conj l (conj m r))

conjTests :: TestTree
conjTests = testGroup "Conj" [conjid, conjcomm] -- [, conjassoc]

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

------------------------- Main -----------------------------------------
main :: IO ()
main = defaultMain $
  adjustOption (const $ QuickCheckTests 1000) $
  adjustOption (const $ QuickCheckMaxSize 1000) $
  testGroup "Unify Tests" $
    [ eqTests
    , neqTests
    , freshTests
    , conjTests
    , disconjTests
    , successTests
    , failureTests
    ]
