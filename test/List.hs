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
  :: LispType ix
  -> LispTerm (List ix)
  -> LispTerm (List ix)
  -> LispTerm (List ix)
  -> Predicate LispTermF
appendo typ l r o =
  conde [ program [ l === inject (Nil typ)
                  , o === r
                  ]
        , fresh typ $ \h ->
            fresh (HFix $ iTList typ) $ \t ->
              fresh (HFix $ iTList typ) $ \o' ->
                 program [ inject (Cons typ h t)   === l
                         , appendo typ t r o'
                         , inject (Cons typ h o')  === o
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

listTest :: forall ix. String -> Integer -> LispType ix -> (LispTerm ix -> Predicate LispTermF) -> [LispTerm ix] -> TestTree
listTest testName n typ query expectedAnswers =
  testCase testName $
  case runN n typ query of
    []      -> assertFailure "no results"
    results -> go results expectedAnswers
  where
    go :: [(Some LispTerm, [Some (Neq LispTermF)])] -> [LispTerm ix] -> Assertion
    go []               []     = return ()
    go ((Some t, _):rs) (a:as) = assertHEqual t a >> go rs as
    go ((Some t, _):_)  []     = assertFailure $ "more results than answers, next result: " ++ hshow t
    go _                (a:_)  = assertFailure $ "no more results while expecting more answers, e.g.: " ++ hshow a

appendTest :: String -> Integer -> LispType ix -> LispTerm (List ix) -> LispTerm (List ix) -> LispTerm (List ix) -> TestTree
appendTest testName n typ xs ys zs =
  listTest testName n (HFix $ inj $ TList $ typ) (\q -> appendo typ xs ys q) [zs]

appendTest' :: String -> LispType ix -> [LispTermF LispTerm ix] -> [LispTermF LispTerm ix] -> [LispTermF LispTerm ix] -> TestTree
appendTest' testName typ xs ys zs =
  appendTest testName 1 typ (ilist typ xs) (ilist typ ys) (ilist typ zs)

atomType :: LispType Atom
atomType = HFix $ iTAtom

listOfAtomsType :: LispType (List Atom)
listOfAtomsType = HFix $ iTList $ atomType

appendTests :: TestTree
appendTests = testGroup "append tests"
  [ appendTest'
      "append #1"
      atomType
      []
      []
      []
  , appendTest'
      "append #2"
      atomType
      []
      [iAtom "bar"]
      [iAtom "bar"]
  , appendTest'
      "append #3"
      atomType
      [iAtom "foo"]
      []
      [iAtom "foo"]
  , appendTest'
      "append #4"
      atomType
      [iAtom "foo"]
      [iAtom "bar"]
      [iAtom "foo", iAtom "bar"]
  , appendTest'
      "append #5"
      atomType
      [iAtom "foo", iAtom "bar", iAtom "baz"]
      [iAtom "x", iAtom "y", iAtom "z"]
      [iAtom "foo", iAtom "bar", iAtom "baz", iAtom "x", iAtom "y", iAtom "z"]
  , listTest
      "append, infer input"
      1
      listOfAtomsType
      (\q -> appendo
               atomType
               q
               (ilist atomType [])
               (ilist atomType [iAtom "foo", iAtom "bar"]))
      [ilist atomType [iAtom "foo", iAtom "bar"]]
  , appendTest'
      "append 2d lists #1"
      listOfAtomsType
      [ list atomType [iAtom "foo"]
      , list atomType [iAtom "bar", iAtom "baz"]
      ]
      [ list atomType [iAtom "x", iAtom "y"]
      , list atomType [iAtom "z"]
      ]
      [ list atomType [iAtom "foo"]
      , list atomType [iAtom "bar", iAtom "baz"]
      , list atomType [iAtom "x", iAtom "y"]
      , list atomType [iAtom "z"]
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
