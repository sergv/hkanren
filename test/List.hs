{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}

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
  :: forall ix.
     (TypeI (LispTermF LispTerm) ix, TypeI (LispTermF LispTerm) (List ix))
  => LispTerm (List ix)
  -> LispTerm (List ix)
  -> LispTerm (List ix)
  -> Predicate LispTermF
appendo l r o =
  conde [ program [ l === inject (Nil singType)
                  , o === r
                  ]
        , fresh $ \h ->
            fresh $ \(t :: LispTerm (List ix)) ->
              fresh $ \o' ->
                 program [ inject (Cons singType h t)   === l
                         , appendo t r o'
                         , inject (Cons singType h o')  === o
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
  :: forall ix. (TypeI (LispTermF LispTerm) ix, TypeI (LispTermF LispTerm) (List ix))
  => String
  -> Integer
  -> (LispTerm ix -> Predicate LispTermF)
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
  :: forall ix.
     ( TypeI (LispTermF LispTerm) ix
     , TypeI (LispTermF LispTerm) (List ix)
     , TypeI (LispTermF LispTerm) (List (List ix))
     )
  => String
  -> Integer
  -> LispTerm (List ix)
  -> LispTerm (List ix)
  -> LispTerm (List ix)
  -> TestTree
appendTest testName n xs ys zs =
  listTest
    testName
    n
    (\q -> appendo xs ys q)
    [zs]

appendTest'
  :: String
  -> [LispTermF LispTerm Atom]
  -> [LispTermF LispTerm Atom]
  -> [LispTermF LispTerm Atom]
  -> TestTree
appendTest' testName xs ys zs =
  appendTest
    testName
    1
    (ilist xs :: LispTerm (List Atom))
    (ilist ys :: LispTerm (List Atom))
    (ilist zs :: LispTerm (List Atom))

-- atomType :: LispType Atom
-- atomType = HFix $ iTAtom
--
-- listOfAtomsType :: LispType (List Atom)
-- listOfAtomsType = HFix $ iTList $ atomType

appendTests :: TestTree
appendTests = testGroup "append tests"
  [ appendTest'
      "append #1"
      ([] :: [LispTermF LispTerm Atom])
      []
      []
  , appendTest'
      "append #2"
      ([] :: [LispTermF LispTerm Atom])
      [iAtom "bar"]
      [iAtom "bar"]
  , appendTest'
      "append #3"
      ([iAtom "foo"] :: [LispTermF LispTerm Atom])
      []
      [iAtom "foo"]
  , appendTest'
      "append #4"
      ([iAtom "foo"] :: [LispTermF LispTerm Atom])
      [iAtom "bar"]
      [iAtom "foo", iAtom "bar"]
  , appendTest'
      "append #5"
      ([iAtom "foo", iAtom "bar", iAtom "baz"] :: [LispTermF LispTerm Atom])
      [iAtom "x", iAtom "y", iAtom "z"]
      [iAtom "foo", iAtom "bar", iAtom "baz", iAtom "x", iAtom "y", iAtom "z"]
  -- , listTest
  --     "append, infer input"
  --     1
  --     (\q -> appendo
  --              q
  --              (ilist [])
  --              (ilist [iAtom "foo", iAtom "bar"]))
  --     ([ilist [iAtom "foo", iAtom "bar"]] :: [LispTermF LispTerm Atom])
  -- , appendTest'
  --     "append 2d lists #1"
  --     [ list ([iAtom "foo"] :: [LispTermF LispTerm Atom])
  --     , list [iAtom "bar", iAtom "baz"]
  --     ]
  --     [ list [iAtom "x", iAtom "y"]
  --     , list [iAtom "z"]
  --     ]
  --     [ list [iAtom "foo"]
  --     , list [iAtom "bar", iAtom "baz"]
  --     , list [iAtom "x", iAtom "y"]
  --     , list [iAtom "z"]
  --     ]
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
