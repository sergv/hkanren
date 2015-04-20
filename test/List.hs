{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RebindableSyntax    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Main where

import Control.Monad (unless)
import qualified Control.Monad as Monad
import Data.HOrdering
import Data.HUtils
import Language.HKanren (TypeI, Neq, Term)
import Language.HKanren.Syntax
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck hiding ((===))

import LispLists

import Data.String
import Prelude hiding ((>>), (>>=))

-- redefine the syntax
(>>) :: Predicate LispTermF -> Predicate LispTermF -> Predicate LispTermF
(>>) = conj

(>>=) :: (TypeI (LispTermF LispTerm) ix)
      => Fresh ix
      -> (Term LispTermF ix -> Predicate LispTermF)
      -> Predicate LispTermF
(>>=) = fresh

appendo
  :: (TypeI (LispTermF LispTerm) ix)
  => LispTerm (List ix)
  -> LispTerm (List ix)
  -> LispTerm (List ix)
  -> Predicate LispTermF
appendo l r o =
  conde
    (do l ==^ Nil
        o === r)
    (manyFresh $ \h t o' -> do
       Cons h t  ^== l
       appendo t r o'
       Cons h o' ^== o)

assertHEqual
  :: (HEq f, HEqHet f, HShow f)
  => f ix   -- ^ The expected value
  -> f ix'  -- ^ The actual value
  -> Assertion
assertHEqual actual expected =
  unless (actual ==* expected) (assertFailure msg)
  where
    msg = "expected: " ++ hshow expected ++ "\n but got: " ++ hshow actual

listTest
  :: forall ix. (TypeI (LispTermF LispTerm) ix)
  => String
  -> Integer
  -> (LispTerm ix -> Predicate LispTermF)
  -> [LispTerm ix]
  -> TestTree
listTest testName n query expectedAnswers =
  testCase testName $
  case runN n query of
    []      -> assertFailure "no results"
    results -> check results expectedAnswers
  where
    check :: [(LispTerm ix, [Some (Neq LispTermF)])] -> [LispTerm ix] -> Assertion
    check []               []    = return ()
    check ((t, _):rs) (a:as)     = assertHEqual t a Monad.>> check rs as
    check ((t, _):_)  []         = assertFailure $ "more results than answers, next result: " ++ hshow t
    check _                (a:_) = assertFailure $ "no more results while expecting more answers, e.g.: " ++ hshow a

appendTest
  :: (TypeI (LispTermF LispTerm) ix)
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
  :: (TypeI (LispTermF LispTerm) ix)
  => String
  -> [LispTermF LispTerm ix]
  -> [LispTermF LispTerm ix]
  -> [LispTermF LispTerm ix]
  -> TestTree
appendTest' testName xs ys zs =
  appendTest
    testName
    1
    (ilist xs)
    (ilist ys)
    (ilist zs)

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
  , listTest
      "append, infer input"
      1
      (\q -> appendo
               q
               (ilist [])
               (ilist [iAtom "foo", iAtom "bar"]))
      ([ilist [iAtom "foo", iAtom "bar"]] :: [LispTerm (List Atom)])
  , appendTest'
      "append 2d lists #1"
      [ list ([iAtom "foo"] :: [LispTermF LispTerm Atom])
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
  , listTest
      "append 2d, infer input"
      1
      (\q -> appendo
               (ilist
                 [ list ([iAtom "foo"] :: [LispTermF LispTerm Atom])
                 , list [iAtom "bar", iAtom "baz"]
                 ])
               q
               (ilist
                 [ list [iAtom "foo"]
                 , list [iAtom "bar", iAtom "baz"]
                 , list [iAtom "x", iAtom "y"]
                 , list [iAtom "z"]
                 ]))
      ([ilist [ list [iAtom "x", iAtom "y"]
              , list [iAtom "z"]
              ]] :: [LispTerm (List (List Atom))])
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

hcompareIxTest :: (HOrdHet f) => String -> f ix -> f ix' -> Ordering -> TestTree
hcompareIxTest name x y expected =
  testCase name $
  assertEqual "" expected (hordering2ordering (hcompareIx x y))

-- lisp term ordered naturally
type OrderedLispTermF = AtomF :+: ListF
type OrderedLispTerm = Term OrderedLispTermF

-- lisp term ordered unnatuarlly but this ordering should also be acceptable
type ReversedLispTermF = ListF :+: AtomF
type ReversedLispTerm = Term ReversedLispTermF

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
          (inj (Atom "foo") :: OrderedLispTermF OrderedLispTerm Atom)
          (inj (Atom "bar") :: OrderedLispTermF OrderedLispTerm Atom)
          EQ
      , hcompareIxTest
          "atom < [atom]"
          (inj (Atom "foo") :: OrderedLispTermF OrderedLispTerm Atom)
          (inj Nil          :: OrderedLispTermF OrderedLispTerm (List Atom))
          LT
      , hcompareIxTest
          "[atom] > atom"
          (inj Nil          :: OrderedLispTermF OrderedLispTerm (List Atom))
          (inj (Atom "foo") :: OrderedLispTermF OrderedLispTerm Atom)
          GT
      , hcompareIxTest
          "[atom] == [atom]"
          (inj Nil :: OrderedLispTermF OrderedLispTerm (List Atom))
          (inj Nil :: OrderedLispTermF OrderedLispTerm (List Atom))
          EQ
      , hcompareIxTest
          "[atom] == [atom] #2"
          (inj Nil :: OrderedLispTermF OrderedLispTerm (List Atom))
          (inj (Cons (inject (Atom "foo"))
                     (inject Nil)) :: OrderedLispTermF OrderedLispTerm (List Atom))
          EQ
      ]
  , testGroup "reversed term"
      [ hcompareIxTest
          "atom : LispType == atom : LispType"
          (inj (Atom "foo") :: ReversedLispTermF ReversedLispTerm Atom)
          (inj (Atom "bar") :: ReversedLispTermF ReversedLispTerm Atom)
          EQ
      , hcompareIxTest
          "atom < [atom]"
          (inj (Atom "foo") :: ReversedLispTermF ReversedLispTerm Atom)
          (inj Nil          :: ReversedLispTermF ReversedLispTerm (List Atom))
          GT
      , hcompareIxTest
          "[atom] > atom"
          (inj Nil          :: ReversedLispTermF ReversedLispTerm (List Atom))
          (inj (Atom "foo") :: ReversedLispTermF ReversedLispTerm Atom)
          LT
      , hcompareIxTest
          "[atom] == [atom]"
          (inj Nil :: ReversedLispTermF ReversedLispTerm (List Atom))
          (inj Nil :: ReversedLispTermF ReversedLispTerm (List Atom))
          EQ
      , hcompareIxTest
          "[atom] == [atom] #2"
          (inj Nil :: ReversedLispTermF ReversedLispTerm (List Atom))
          (inj (Cons (inject (Atom "foo"))
                     (inject Nil)) :: ReversedLispTermF ReversedLispTerm (List Atom))
          EQ
      ]
  ]

main :: IO ()
main = defaultMain $
  adjustOption (const $ QuickCheckTests 1000) $
  adjustOption (const $ QuickCheckMaxSize 1000) $
  testGroup "List Tests"
    [ appendTests
    , ixComparisonTests
    ]
