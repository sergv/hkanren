module QuickCheckHelper where
import Control.Applicative
import Language.DSKanren
import Test.QuickCheck hiding ((===))

hasSolution :: Predicate -> Bool
hasSolution = runFor1
  where runFor1 p = case run (const p) of
          _ : _ -> True
          []    -> False


two :: Applicative f => f a -> f (a, a)
two f = (,) <$> f <*> f

three :: Applicative f => f a -> f (a, a, a)
three f = (,,) <$> f <*> f <*> f

mkTerm :: [Term] -> Gen Term
mkTerm vars = oneof $
  case vars of
   [] -> closedConstructs
   _  -> elements vars : closedConstructs
  where closedConstructs = [ Atom <$> (listOf . elements $ ['a' .. 'z'])
                           , Pair <$> mkTerm vars <*> mkTerm vars]

mkPred :: [Term] -> Gen Predicate
mkPred vars = -- TODO, Fit fresh in here somehow
  oneof
  [ disconj <$> mkPred vars <*> mkPred vars
  , conj    <$> mkPred vars <*> mkPred vars
  , (===)   <$> mkTerm vars <*> mkTerm vars
  , (=/=)   <$> mkTerm vars <*> mkTerm vars
  , elements [success, failure]]

instance Arbitrary Predicate where
  arbitrary = mkPred [currentGoal]
