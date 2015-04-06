{-# LANGUAGE OverloadedStrings #-}
module Main where

import Data.HUtils
import Language.HKanren
import Test.Tasty.QuickCheck hiding ((===))
import Test.Tasty
import QuickCheckHelper

appendo :: LispTermF LispTerm ix -> LispTermF LispTerm ix -> LispTermF LispTerm ix -> Predicate LispTermF
appendo l r o =
  conde [ program [ l === inj (Atom "nil")
                  , o === r
                  ]
        , fresh templateAtom $ \h ->
            fresh templatePair $ \t ->
              fresh templatePair $ \o' ->
                program [ inject (Pair h t) === l
                        , appendo t r o'
                        , inject (Pair h o') === o
                        ]
        ]

heado :: LispTerm ix -> LispTerm ix -> Predicate LispTermF
heado l h = fresh $ \t -> Pair h t === l

tailo :: LispTerm ix -> LispTerm ix -> Predicate LispTermF
tailo l t = fresh $ \h -> Pair h t === l

isAppend :: TestTree
isAppend = testProperty "Head Works"
           . mapSize (const 3)
           . forAll (two . listOf1 $ mkTerm [])
           $ \(l, r) -> case runN 1 $ appendo (list l) (list r) of
                         (t, _) : _ -> t == list (l ++ r)
                         _ -> False

isHead :: TestTree
isHead = testProperty "Head Works"
         . mapSize (const 3)
         . forAll (listOf1 $ mkTerm [])
         $ \terms -> case runN 1 $ heado (list terms) of
                      (t, _) : _ -> t == head terms
                      _ -> False

isTail :: TestTree
isTail = testProperty "Tail Works"
         . mapSize (const 3)
         . forAll (listOf1 $ mkTerm [])
         $ \terms -> case runN 1 $ tailo (list terms) of
                      (t, _) : _ -> t == list (tail terms)
                      _ -> False

main :: IO ()
main = defaultMain $
  adjustOption (const $ QuickCheckTests 1000) $
  adjustOption (const $ QuickCheckMaxSize 1000) $
  testGroup "List Tests"
    [ isHead
    , isTail
    ]
