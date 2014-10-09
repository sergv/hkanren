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
heado h l = fresh $ \t -> Pair h t === l

tailo :: Term -> Term -> Predicate
tailo t l = fresh $ \h -> Pair h t === l


isAppend :: TestTree
isAppend = testProperty "Head Works"
           . forAll (two . listOf1 $ mkTerm [currentGoal])
           $ \(l, r) -> case runN 1 $ appendo (list l) (list r) of
                         (t, _) : _ -> t == list (l ++ r)
                         _ -> False


isHead :: TestTree
isHead = testProperty "Head Works"
         . forAll (listOf1 $ mkTerm [currentGoal])
         $ \terms -> case runN 1 $ \h -> heado h (list terms) of
                      (t, _) : _ -> t == head terms
                      _ -> False

isTail :: TestTree
isTail = testProperty "Tail Works"
         . forAll (listOf1 $ mkTerm [currentGoal])
         $ \terms -> case runN 1 $ \h -> tailo h (list terms) of
                      (t, _) : _ -> t == list (tail terms)
                      _ -> False

main :: IO ()
main = defaultMain (testGroup "List Tests" [isAppend, isHead, isTail])
