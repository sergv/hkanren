-- | Test to ensure that unification function as intended.
module Main where
import Language.DSKanren
import Test.Tasty

main :: IO ()
main = defaultMain (testGroup "List Tests" [])
