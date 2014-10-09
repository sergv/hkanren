{-# LANGUAGE OverloadedStrings #-}
module Main where
import Language.DSKanren
import Test.Tasty.QuickCheck hiding ((===))
import Test.Tasty
import QuickCheckHelper

appendo :: Term -> Term -> Term -> Predicate
appendo l r o =
  conde [ program [l === "nil", o === r]
        , manyFresh $ \h t o' ->
            program [ Pair h t === l
                    , appendo t r o'
                    , Pair h o' === o ]]

heado :: Term -> Term -> Predicate
heado l h = fresh $ \t -> Pair h t === l

tailo :: Term -> Term -> Predicate
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
main = defaultMain (testGroup "List Tests" [isHead, isTail])
