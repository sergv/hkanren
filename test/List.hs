{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RebindableSyntax    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Main where

import Control.Arrow (first)
import Control.Monad (unless)
import qualified Control.Monad as Monad
import Data.HOrdering
import Data.HUtils
import Data.Monoid
import qualified Data.Text.Lazy as T
import Language.HKanren.Functions.List
import Language.HKanren.Functions.Nat
import qualified Language.HKanren.SafeLVar as Safe
import Language.HKanren.Syntax
import Language.HKanren.Types.List
import Language.HKanren.Types.Nat
import Text.PrettyPrint.Leijen.Text (Pretty(..), displayT, renderPretty)
import qualified Text.PrettyPrint.Leijen.Text as PP
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck hiding ((===))

import LispLists

import Data.List (sortBy)
import Data.Ord (comparing)
import Data.String
import Prelude hiding ((>>), (>>=))

-- redefine the syntax
(>>) :: Predicate LispVar -> Predicate LispVar -> Predicate LispVar
(>>) = conj

(>>=) :: Fresh LispVar a
      -> (a -> Predicate LispVar)
      -> Predicate LispVar
(>>=) = withFresh

assertHEqual
  :: (HEq f, HEqHet f, HShow f)
  => String -- ^ prefix
  -> f ix   -- ^ The expected value
  -> f ix'  -- ^ The actual value
  -> Assertion
assertHEqual prefix actual expected =
  unless (actual ==* expected) (assertFailure msg)
  where
    msg = prefix ++ "expected: " ++ hshow expected ++ "\n but got: " ++ hshow actual

failingListTest
  :: forall ix. (TypeI (LispTermF LispTerm) ix)
  => String
  -> (LispTerm ix -> Predicate LispVar)
  -> TestTree
failingListTest testName query =
  testCase testName $
  case runN 1 query of
    [] -> return ()
    _  -> assertFailure "predicate unexpectedly succeeded"

lispTest
  :: forall ix. (TypeI (LispTermF LispTerm) ix)
  => String
  -> Int
  -> (LispTerm ix -> Predicate LispVar)
  -> [LispTerm ix]
  -> TestTree
lispTest testName n query expectedAnswers =
  testCase testName $
  case runN n query of
    []      -> assertFailure "no results"
    results -> checkSorted results expectedAnswers

checkSorted :: [(LispTerm ix, [Some (Neq LispVar)])] -> [LispTerm ix] -> Assertion
checkSorted results expectedAnswers = do
  unless (resultsCount == expectedAnswersCount) $
    assertFailure $ "expected " ++ show expectedAnswersCount ++ " results but got " ++ show resultsCount
  check (sortBy (comparing (Some . fst)) results) (sortBy (comparing Some) expectedAnswers)
  where
    (>>) = (Monad.>>)
    resultsCount = length results
    expectedAnswersCount = length expectedAnswers

check :: [(LispTerm ix, [Some (Neq LispVar)])] -> [LispTerm ix] -> Assertion
check xs ys = go xs ys
  where
    prefix = display $ PP.align ("results  = " <> pretty (map (first Some) xs)) PP.<$>
                       "|results|  = " <> pretty (length xs) PP.<$>
                       PP.align ("expected = " <> pretty (map Some ys)) PP.<$>
                       "|expected| = " <> pretty (length ys) <> PP.line
    go []          []     = return ()
    go ((t, _):rs) (a:as) = assertHEqual prefix t a Monad.>> go rs as
    go ((t, _):_)  []     = assertFailure $ "more results than answers, next result: " ++ hshow t
    go _           (a:_)  = assertFailure $ "no more results while expecting more answers, e.g.: " ++ hshow a

display :: (Pretty a) => a -> String
display = T.unpack . displayT . renderPretty 0.9 100 . pretty

appendTest
  :: (TypeI (LispTermF LispTerm) ix)
  => String
  -> [LispTerm ix]
  -> [LispTerm ix]
  -> [LispTerm ix]
  -> TestTree
appendTest testName xs ys zs =
  lispTest
    testName
    1
    (\q -> appendo (list xs) (list ys) q)
    [list zs]

appendTests :: TestTree
appendTests = testGroup "append tests"
  [ appendTest
      "append 1d #1"
      ([] :: [LispTerm Atom])
      []
      []
  , appendTest
      "append 1d #2"
      []
      [iAtom "bar"]
      [iAtom "bar"]
  , appendTest
      "append 1d #3"
      [iAtom "foo"]
      []
      [iAtom "foo"]
  , appendTest
      "append 1d #4"
      [iAtom "foo"]
      [iAtom "bar"]
      [iAtom "foo", iAtom "bar"]
  , appendTest
      "append 1d #5"
      [iAtom "foo", iAtom "bar", iAtom "baz"]
      [iAtom "x", iAtom "y", iAtom "z"]
      [iAtom "foo", iAtom "bar", iAtom "baz", iAtom "x", iAtom "y", iAtom "z"]
  , lispTest
      "append 1d, infer input"
      1
      (\q -> appendo
               q
               (list [])
               (list [iAtom "foo", iAtom "bar"]))
      [list [iAtom "foo", iAtom "bar"]]
  , appendTest
      "append 2d #1"
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
  , lispTest
      "append 2d, infer input"
      1
      (\q -> appendo
               (list
                 [ list [iAtom "foo"]
                 , list [iAtom "bar", iAtom "baz"]
                 ])
               q
               (list
                 [ list [iAtom "foo"]
                 , list [iAtom "bar", iAtom "baz"]
                 , list [iAtom "x", iAtom "y"]
                 , list [iAtom "z"]
                 ]))
      [list [ list [iAtom "x", iAtom "y"]
            , list [iAtom "z"]
            ]]
  ]

succeedingMemberTest
  :: (TypeI (LispTermF LispTerm) ix)
  => String
  -> LispTerm ix
  -> [LispTerm ix]
  -> TestTree
succeedingMemberTest name x xs =
  lispTest
    name
    1
    (\q -> do
      member x xs'
      x === q)
    [x]
  where
    xs' = list xs

failingMemberTest
  :: (TypeI (LispTermF LispTerm) ix)
  => String
  -> LispTerm ix
  -> [LispTerm ix]
  -> TestTree
failingMemberTest name x xs =
  failingListTest
    name
    (\q -> do
      member x xs'
      x === q)
  where
    xs' = list xs

memberQuery
  :: (TypeI (LispTermF LispTerm) ix)
  => String
  -> [LispTerm ix]
  -> [LispTerm ix]
  -> TestTree
memberQuery name xs expectedAnswers =
  lispTest
    name
    (length xs)
    (\q -> do
      member q xs')
    expectedAnswers
  where
    xs' = list xs

memberTests :: TestTree
memberTests = testGroup "append tests"
  [ succeedingMemberTest
      "member succeeds #1"
      (iAtom "foo")
      [iAtom "foo", iAtom "bar"]
  , succeedingMemberTest
      "member succeeds #2"
      (iAtom "bar")
      [iAtom "foo", iAtom "bar"]
  , failingMemberTest
      "member fails #1"
      (iAtom "baz")
      [iAtom "foo", iAtom "bar"]
  , memberQuery
      "member query #1"
      [iAtom "foo", iAtom "bar"]
      [iAtom "foo", iAtom "bar"]
  ]

plusoQuery
  :: String
  -> Int
  -> Int
  -> Int
  -> TestTree
plusoQuery testName x y expected =
  lispTest
    testName
    1
    (\q -> pluso (int2nat x) (int2nat y) q)
    [int2nat expected]

natTests :: TestTree
natTests = testGroup "nat tests"
  [ testGroup "pluso"
      [ plusoQuery "0 + 0 = 0" 0 0 0
      , plusoQuery "0 + 1 = 1" 0 1 1
      , plusoQuery "1 + 0 = 1" 1 0 1
      , plusoQuery "1 + 1 = 2" 1 1 2
      ]
  ]


allUniqueQuery
  :: (TypeI (LispTermF LispTerm) ix)
  => String
  -> [LispTerm ix]
  -> [LispTerm (List ix)]
  -> TestTree
allUniqueQuery name xs expectedAnswers =
  lispTest
    name
    (length expectedAnswers)
    (\q -> do
      allo (\x -> member x xs') q
      allUnique q)
    expectedAnswers
  where
    xs' = list xs

allUniqueTests :: TestTree
allUniqueTests = testGroup "append tests"
  [ allUniqueQuery
      "allUnique query #1"
      [iAtom "foo", iAtom "bar"]
      [ list []
      , list [iAtom "bar"]
      , list [iAtom "foo"]
      , list [iAtom "bar", iAtom "foo"]
      ]
  ]

hcompareIxTest :: (HOrdHet f) => String -> f ix -> f ix' -> Ordering -> TestTree
hcompareIxTest name x y expected =
  testCase name $
  assertEqual "" expected (hordering2ordering (hcompareIx x y))

-- lisp term ordered naturally
type OrderedLispTermF = AtomF :+: ListF
type OrderedLispTerm = Term (Safe.LVar OrderedLispTermF)

-- lisp term ordered unnatuarlly but this ordering should also be acceptable
type ReversedLispTermF = ListF :+: AtomF
type ReversedLispTerm = Term (Safe.LVar ReversedLispTermF)

ixComparisonTests :: TestTree
ixComparisonTests = testGroup "index comparison tests"
  [ hcompareIxTest
      "atom == atom"
      (Atom "foo")
      (Atom "bar")
      EQ
  , testGroup "naturally ordered term"
      [ hcompareIxTest
          "atom : LispType == atom : LispType"
          (iAtom "foo" :: OrderedLispTerm Atom)
          (iAtom "bar" :: OrderedLispTerm Atom)
          EQ
      , hcompareIxTest
          "atom < [atom]"
          (iAtom "foo" :: OrderedLispTerm Atom)
          (iNil        :: OrderedLispTerm (List Atom))
          LT
      , hcompareIxTest
          "[atom] > atom"
          (iNil        :: OrderedLispTerm (List Atom))
          (iAtom "foo" :: OrderedLispTerm Atom)
          GT
      , hcompareIxTest
          "[atom] == [atom]"
          (iNil :: OrderedLispTerm (List Atom))
          (iNil :: OrderedLispTerm (List Atom))
          EQ
      , hcompareIxTest
          "[atom] == [atom] #2"
          (iNil :: OrderedLispTerm (List Atom))
          (iCons (iAtom "foo")
                 (iNil) :: OrderedLispTerm (List Atom))
          EQ
      ]
  , testGroup "reversed term"
      [ hcompareIxTest
          "atom : LispType == atom : LispType"
          (iAtom "foo" :: ReversedLispTerm Atom)
          (iAtom "bar" :: ReversedLispTerm Atom)
          EQ
      , hcompareIxTest
          "atom < [atom]"
          (iAtom "foo" :: ReversedLispTerm Atom)
          (iNil        :: ReversedLispTerm (List Atom))
          GT
      , hcompareIxTest
          "[atom] > atom"
          (iNil        :: ReversedLispTerm (List Atom))
          (iAtom "foo" :: ReversedLispTerm Atom)
          LT
      , hcompareIxTest
          "[atom] == [atom]"
          (iNil :: ReversedLispTerm (List Atom))
          (iNil :: ReversedLispTerm (List Atom))
          EQ
      , hcompareIxTest
          "[atom] == [atom] #2"
          (iNil :: ReversedLispTerm (List Atom))
          (inj (iCons (iAtom "foo")
                      (iNil)) :: ReversedLispTerm (List Atom))
          EQ
      ]
  ]


listOrdInstanceTests :: TestTree
listOrdInstanceTests = testGroup "comparison instanes for lists"
  [ testCase "list of lists of atoms sorting with sortBy" $ do
      let xs :: [LispTerm (List Atom)]
          xs = [ list []
               , list [iAtom "bar"]
               , list [iAtom "foo"]
               , list [iAtom "foo", iAtom "bar"]
               ]
          ys = sortBy (comparing Some) xs
      assertEqual
        "sorted list has different number of items that unsorted one"
        (length xs)
        (length ys)
      assertBool "sorted list is not actually sorted" $ isSorted $ map Some ys
      assertBool "sorted list is not actually h-sorted" $ isHSorted ys
  ]
  where
    (>>) = (Monad.>>)

isSorted :: (Ord a) => [a] -> Bool
isSorted []            = True
isSorted [_]           = True
isSorted (x:xs@(x':_)) = x <= x' && isSorted xs

isHSorted :: (HOrd a) => [a ix] -> Bool
isHSorted []  = True
isHSorted [_] = True
isHSorted (x:xs@(x':_)) =
  case hcompare x x' of
    LT -> isHSorted xs
    EQ -> isHSorted xs
    GT -> False

main :: IO ()
main = defaultMain $
  adjustOption (const $ QuickCheckTests 1000) $
  adjustOption (const $ QuickCheckMaxSize 1000) $
  testGroup "List Tests"
    [ testGroup "functions"
        [ appendTests
        , memberTests
        , allUniqueTests
        ]
    , natTests
    , ixComparisonTests
    , listOrdInstanceTests
    ]
