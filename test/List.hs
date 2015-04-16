{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Control.Monad
import Data.HOrdering
import Data.HUtils
import Language.HKanren
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck hiding ((===))
import QuickCheckHelper

appendo
  :: (SingI ix)
  => LispTerm (List ix)
  -> LispTerm (List ix)
  -> LispTerm (List ix)
  -> Predicate LispTermF
appendo l r o =
  conde [ program [ l === inject (Nil sing)
                  , o === r
                  ]
        , fresh $ \h ->
            fresh $ \t ->
              fresh $ \o' ->
                 program [ inject (Cons sing h t)   === l
                         , appendo t r o'
                         , inject (Cons sing h o')  === o
                         ]
        ]

assertHEqual
  :: (HEqHet f, HShow f)
  => f ix   -- ^ The expected value
  -> f ix'  -- ^ The actual value
  -> Assertion
assertHEqual actual expected =
  unless (actual ==* expected) (assertFailure msg)
  where
    msg = "expected: " ++ hshow expected ++ "\n but got: " ++ hshow actual

listTest
  :: forall ix. (SingI ix, HOrdHet Sing)
  => String
  -> Integer
  -> (LispTerm ix
  -> Predicate LispTermF)
  -> [LispTerm ix]
  -> TestTree
listTest testName n query expectedAnswers =
  testCase testName $
  case runN n query of
    []      -> assertFailure "no results"
    results -> go results expectedAnswers
  where
    go :: [(Some LispTerm, [Some (Neq LispTermF)])] -> [LispTerm ix] -> Assertion
    go []               []     = return ()
    go ((Some t, _):rs) (a:as) = assertHEqual t a >> go rs as
    go ((Some t, _):_)  []     = assertFailure $ "more results than answers, next result: " ++ hshow t
    go _                (a:_)  = assertFailure $ "no more results while expecting more answers, e.g.: " ++ hshow a

appendTest
  :: (SingI ix, HOrdHet Sing)
  => String
  -> Integer
  -> LispTerm (List ix)
  -> LispTerm (List ix)
  -> LispTerm (List ix)
  -> TestTree
appendTest testName n xs ys zs =
  listTest testName n (\q -> appendo xs ys q) [zs]

appendTest'
  :: (SingI ix, HOrdHet Sing)
  => String
  -> [LispTermF LispTerm ix]
  -> [LispTermF LispTerm ix]
  -> [LispTermF LispTerm ix]
  -> TestTree
appendTest' testName xs ys zs =
  appendTest testName 1 (ilist xs) (ilist ys) (ilist zs)

-- atomType :: LispType Atom
-- atomType = HFix $ iTAtom
--
-- listOfAtomsType :: LispType (List Atom)
-- listOfAtomsType = HFix $ iTList $ atomType

appendTests :: TestTree
appendTests = testGroup "append tests"
  [ appendTest'
      "append #1"
      []
      []
      []
  , appendTest'
      "append #2"
      []
      [iAtom "bar"]
      [iAtom "bar"]
  , appendTest'
      "append #3"
      [iAtom "foo"]
      []
      [iAtom "foo"]
  , appendTest'
      "append #4"
      [iAtom "foo"]
      [iAtom "bar"]
      [iAtom "foo", iAtom "bar"]
  , appendTest'
      "append #5"
      [iAtom "foo", iAtom "bar", iAtom "baz"]
      [iAtom "x", iAtom "y", iAtom "z"]
      [iAtom "foo", iAtom "bar", iAtom "baz", iAtom "x", iAtom "y", iAtom "z"]
  , listTest
      "append, infer input"
      1
      (\q -> appendo
               q
               (ilist [])
               (ilist [iAtom "foo", iAtom "bar"]))
      [ilist [iAtom "foo", iAtom "bar"]]
  , appendTest'
      "append 2d lists #1"
      [ list [iAtom "foo"]
      , list [iAtom "bar", iAtom "baz"]
      ]
      [ list [iAtom "x", iAtom "y"]
      , list [iAtom "z"]
      ]
      [ list [iAtom "foo"]
      , list [iAtom "bar", iAtom "baz"]
      , list [iAtom "x", iAtom "y"]
      , list [iAtom "z"]
      ]
  ]

-- heado :: LispTerm ix -> LispTerm ix -> Predicate LispTermF
-- heado l h = fresh $ \t -> inject (Pair h t) === l
--
-- tailo :: LispTerm ix -> LispTerm ix -> Predicate LispTermF
-- tailo l t = fresh $ \h -> inject (Pair h t) === l
--
-- isAppend :: TestTree
-- isAppend = testProperty "Append Works"
--            . mapSize (const 3)
--            . forAll (two . listOf1 $ mkTerm [])
--            $ \(l, r) -> case runN 1 atomType $ appendo (list l) (list r) of
--                           (t, _) : _ -> t == list (l ++ r)
--                           _ -> False
--
-- isHead :: TestTree
-- isHead = testProperty "Head Works"
--          . mapSize (const 3)
--          . forAll (listOf1 $ mkTerm [])
--          $ \terms -> case runN 1 $ heado (list terms) of
--                       (t, _) : _ -> t == head terms
--                       _ -> False
--
-- isTail :: TestTree
-- isTail = testProperty "Tail Works"
--          . mapSize (const 3)
--          . forAll (listOf1 $ mkTerm [])
--          $ \terms -> case runN 1 $ tailo (list terms) of
--                       (t, _) : _ -> t == list (tail terms)
--                       _ -> False
--
-- main :: IO ()
-- main = defaultMain $
--   adjustOption (const $ QuickCheckTests 1000) $
--   adjustOption (const $ QuickCheckMaxSize 1000) $
--   testGroup "List Tests"
--     [ isAppend
--     -- , isHead
--     -- , isTail
--     ]


main :: IO ()
main = defaultMain $
  adjustOption (const $ QuickCheckTests 1000) $
  adjustOption (const $ QuickCheckMaxSize 1000) $
  testGroup "List Tests"
    [ appendTests
    ]
