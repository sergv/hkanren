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

two :: Applicative f => f a -> f (a, a)
two f = (,) <$> f <*> f

three :: Applicative f => f a -> f (a, a, a)
three f = (,,) <$> f <*> f <*> f

forTerm :: Testable a => (Term -> a) -> Property
forTerm = forAll (mkTerm [currentGoal])

forTerm2 :: Testable a => (Term -> Term -> a) -> Property
forTerm2 p = forAll (two $ mkTerm [currentGoal]) $ \(l, r) -> p l r

forTerm3 :: Testable a => (Term -> Term -> Term -> a) -> Property
forTerm3 p = forAll (three $ mkTerm [currentGoal]) $ \(l, m, r) -> p l m r

forPred :: Testable a => (Predicate -> a) -> Property
forPred = forAll (mkPred [currentGoal]) . (. toPredicate)

forPred2 :: Testable a => (Predicate -> Predicate -> a) -> Property
forPred2 p = forAll (two $ mkPred [currentGoal]) $
             \(l, r) -> p (toPredicate l) (toPredicate r)

forPred3 :: Testable a => (Predicate -> Predicate -> Predicate -> a) -> Property
forPred3 p = forAll (three $ mkPred [currentGoal]) $
             \(l, m, r) -> p (toPredicate l) (toPredicate m) (toPredicate r)
