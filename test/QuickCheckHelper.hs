module QuickCheckHelper where
import Control.Applicative
import Language.DSKanren
import Test.QuickCheck hiding ((===))

data RPred = Conj RPred RPred
           | Disconj RPred RPred
           | Eq Term Term
           | Neq Term Term
           | Tigger
           | Eeyore
           deriving Show

toPredicate :: RPred -> Predicate
toPredicate t =
  case t of
   Conj l r -> conj (toPredicate l) (toPredicate r)
   Disconj l r -> disconj (toPredicate l) (toPredicate r)
   Eq l r -> l === r
   Neq l r -> l =/= r
   Tigger -> success
   Eeyore -> failure

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

mkPred :: [Term] -> Gen RPred
mkPred vars = -- TODO, Fit fresh in here somehow
  oneof
  [ Disconj <$> mkPred vars <*> mkPred vars
  , Conj    <$> mkPred vars <*> mkPred vars
  , Eq   <$> mkTerm vars <*> mkTerm vars
  , Neq   <$> mkTerm vars <*> mkTerm vars
  , elements [Tigger, Eeyore]]

forPred :: (Predicate -> Property) -> Property
forPred = forAll (mkPred [currentGoal]) . (. toPredicate)

forPred2 :: (Predicate -> Predicate -> Property) -> Property
forPred2 p = forAll (two $ mkPred [currentGoal]) $
             \(l, r) -> p (toPredicate l) (toPredicate r)
