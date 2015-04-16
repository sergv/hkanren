{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE EmptyDataDecls            #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

module QuickCheckHelper where

import Control.Monad
import Data.HOrdering
import Data.HUtils
import Data.Monoid
import Data.Type.Equality
import Language.HKanren
-- import Test.QuickCheck hiding ((===), Success, Failure)

data Atom

data AtomF :: (* -> *) -> (* -> *) where
  Atom :: String -> AtomF r Atom

iAtom :: (AtomF :<: h) => String -> h r Atom
iAtom = inj . Atom

instance (AtomF :<: h) => Unifiable AtomF h where
  unify (Atom x) (Atom y) s
    | x == y    = Just s
    | otherwise = Nothing

instance SingI Atom where
  data Sing Atom where
    TAtom :: Sing Atom
  sing = TAtom

-- instance TypeRep AtomF where
--   data TypeOf AtomF e ix where
--     TAtom :: TypeOf AtomF e Atom
--   typeOf (Atom _) = TAtom
--
-- iTAtom :: (TypeOf AtomF :<: h) => h e Atom
-- iTAtom = inj TAtom

instance HEq (AtomF f) where
  heq (Atom x) (Atom y) = x == y

instance HEqHet (AtomF f) where
  heqIx (Atom _) (Atom _) = Just Refl

instance HOrd (AtomF f) where
  hcompare (Atom x) (Atom y) = compare x y

instance HOrdHet (AtomF f) where
  hcompareIx (Atom _) (Atom _) = HEQ Refl

instance HFunctorId AtomF where
  hfmapId _ (Atom n) = Atom n

instance HFunctor AtomF where
  hfmap _ (Atom n) = Atom n

instance HFoldable AtomF where
  hfoldMap _ _ = mempty

instance HShow (AtomF f) where
  hshowsPrec n (Atom str) = \xs -> showParen (n == 11) (\ys -> "Atom " ++ show str ++ ys) xs


data List ix

instance (SingI ix) => SingI (List ix) where
  data Sing (List ix) where
    TList :: Sing ix -> Sing (List ix)
  sing = TList sing

data ListF :: (* -> *) -> (* -> *) where
  Nil  :: Sing ix -> ListF r (List ix)
  Cons :: Sing ix -> r ix -> r (List ix) -> ListF r (List ix)

instance (HFoldable h, HOrdHet Sing, Unifiable h h) => Unifiable ListF h where
  unify (Nil _)       (Nil _)       = return
  unify (Cons _ x xs) (Cons _ y ys) =
    unifyTerms x y >=> unifyTerms xs ys
  unify _ _ = const Nothing

-- instance TypeRep ListF where
--   data TypeOf ListF r ix where
--     TList :: r ix -> TypeOf ListF r (List ix)
--   typeOf (Nil t)      = TList t
--   typeOf (Cons t _ _) = TList t

-- iTList :: (TypeOf ListF :<: h) => r ix -> h r (List ix)
-- iTList = inj . TList

instance (HEq f) => HEq (ListF f) where
  heq (Nil _)       (Nil _)       = True
  heq (Cons _ x xs) (Cons _ y ys) = heq x y && heq xs ys
  heq _             _             = False

instance (HEqHet f, HEqHet Sing) => HEqHet (ListF f) where
  heqIx (Nil t)       (Nil t')       =
    case heqIx t t' of
      Just Refl -> Just Refl
      Nothing   -> Nothing
  heqIx (Nil t)       (Cons t' _ _)  =
    case heqIx t t' of
      Just Refl -> Just Refl
      Nothing   -> Nothing
  heqIx (Cons t _ _)  (Nil t')       =
    case heqIx t t' of
      Just Refl -> Just Refl
      Nothing   -> Nothing
  heqIx (Cons t _x _) (Cons t' _y _) =
    case heqIx t t' of
      Just Refl -> Just Refl
      Nothing   -> Nothing

instance (HOrd f) => HOrd (ListF f) where
  hcompare (Nil _)       (Nil _)       = EQ
  hcompare (Nil _)       (Cons _ _ _)  = LT
  hcompare (Cons _ _ _)  (Nil _)       = GT
  hcompare (Cons _ x xs) (Cons _ y ys) = hcompare x y <> hcompare xs ys

instance (HOrdHet f, HOrdHet Sing) => HOrdHet (ListF f) where
  hcompareIx (Nil t)      (Nil t')      =
    case hcompareIx t t' of
      HLT      -> HLT
      HEQ Refl -> HEQ Refl
      HGT      -> HGT
  hcompareIx (Nil t)      (Cons t' _ _) =
    case hcompareIx t t' of
      HLT      -> HLT
      HEQ Refl -> HEQ Refl
      HGT      -> HGT
  hcompareIx (Cons t _ _) (Nil t')      =
    case hcompareIx t t' of
      HLT      -> HLT
      HEQ Refl -> HEQ Refl
      HGT      -> HGT
  hcompareIx (Cons t _ _) (Cons t' _ _) =
    case hcompareIx t t' of
      HLT      -> HLT
      HEQ Refl -> HEQ Refl
      HGT      -> HGT

instance HFunctorId ListF where
  hfmapId _ (Nil t)       = Nil t
  hfmapId f (Cons t x xs) = Cons t (f x) (f xs)

-- instance HFunctor ListF where
--   hfmap _ (Nil t)       = Nil t
--   hfmap f (Cons t x xs) = Cons t (f x) (f xs)

instance HFoldable ListF where
  hfoldMap _ (Nil _)       = mempty
  hfoldMap f (Cons _ x xs) = f x <> f xs

instance (HShow f) => HShow (ListF f) where
  hshowsPrec _ (Nil _)       = \xs -> "Nil" ++ xs
  hshowsPrec n (Cons _ x xs) =
    \ys -> showParen (n == 11) (\zs -> "Cons " ++ hshowsPrec 11 x (showChar ' ' $ hshowsPrec 11 xs zs)) ys


type LispTermF = ListF :+: AtomF
type LispTerm = Term LispTermF
-- type LispType = Type LispTermF

list :: (SingI ix) => [LispTermF LispTerm ix] -> LispTermF LispTerm (List ix)
list = foldr (\x y -> inj $ Cons sing (HFree x) (HFree y)) (inj $ Nil sing)

ilist :: (SingI ix) => [LispTermF LispTerm ix] -> LispTerm (List ix)
ilist = HFree . list


-- data Pair ix ix'
--
-- data PairF (f :: * -> *) ix where
--   Pair :: f ix -> f ix' -> PairF f (Pair ix ix')
--
-- instance (HFoldable h, HOrdHet (h HUnit), Unifiable h h, PairF :<: h) => Unifiable PairF h where
--   unify (Pair x y) (Pair x' y') =
--     unifyTerms x x' >=> unifyTerms y y'
--
-- instance (HEq f) => HEq (PairF f) where
--   heq (Pair x y) (Pair x' y') = heq x x' && heq y y'
--
-- instance (HEqHet f) => HEqHet (PairF f) where
--   heqIx (Pair x y) (Pair x' y') =
--     case heqIx x x' of
--       Just Refl ->
--         case heqIx y y' of
--           Just Refl -> Just Refl
--           Nothing   -> Nothing
--       Nothing   -> Nothing
--
-- instance (HOrd f) => HOrd (PairF f) where
--   hcompare (Pair x y) (Pair x' y') = hcompare x x' <> hcompare y y'
--
-- instance (HOrdHet f) => HOrdHet (PairF f) where
--   hcompareIx (Pair x y) (Pair x' y') =
--     case hcompareIx x x' of
--       HLT      -> HLT
--       HEQ Refl ->
--         case hcompareIx y y' of
--           HLT      -> HLT
--           HEQ Refl -> HEQ Refl
--           HGT      -> HGT
--       HGT      -> HGT
--
-- instance HFunctor PairF where
--   hfmap f (Pair x y) = Pair (f x) (f y)
--
-- instance HFoldable PairF where
--   hfoldMap f (Pair x y) = f x <> f y
--
-- instance (HShow f) => HShow (PairF f) where
--   hshowsPrec n (Pair x y) = \xs -> showParen (n == 11) (\ys -> "Pair " ++ hshowsPrec 11 x (showChar ' ' $ hshowsPrec 11 y ys)) xs

-- data RPred =
--     Conj RPred RPred
--   | Disconj RPred RPred
--   | forall ix. Eq (LispTerm ix) (LispTerm ix)
--   | forall ix. Neq (LispTerm ix) (LispTerm ix)
--   | Success
--   | Failure
-- instance Show RPred where
--   show _ = "RPred"
--
-- toPredicate :: RPred -> Predicate LispTermF
-- toPredicate t =
--   case t of
--     Conj l r    -> conj (toPredicate l) (toPredicate r)
--     Disconj l r -> disconj (toPredicate l) (toPredicate r)
--     Eq l r      -> l === r
--     Neq l r     -> l =/= r
--     Success     -> success
--     Failure     -> failure
--
-- hasSolution :: (HFunctor h, HFoldable h, Unifiable h h, HOrdHet (h HUnit), AtomF :<: h)
--             => Predicate h -> Bool
-- hasSolution p =
--   case run templateAtom (const p) of
--     []  -> False
--     _:_ -> True
--
-- mkAtomTerm :: Gen (LispTermF LispTerm Atom)
-- mkAtomTerm = inj . Atom <$> (listOf1 $ elements chars)
--
-- -- mkPairTerm :: [LispTerm ix]
-- --            -> [LispTerm ix']
-- --            -> Gen (LispTermF LispTerm (Pair ix ix'))
-- -- mkPairTerm xs ys =
-- --   oneof [return $ inj $ Pair x y | x <- xs, y <- ys]
--
-- mkListTerm :: [Gen (LispTerm ix)] -> Gen [LispTermF LispTerm (List ix)]
-- mkListTerm xs = list <$> listOf xs
--
-- mkTerm1 :: [Some LispTerm] -> Gen (Some (LispTermF LispTerm))
-- mkTerm1 vars = frequency closedConstructs
--   where
--     closedConstructs =
--       [ (10, Some <$> mkAtomTerm)
--       , (1,  ((\(Some x) (Some y) -> Some $ inj $ Pair x y) <$> mkTerm vars <*> mkTerm vars))
--       -- , (1,  ((\(Some x) (Some y) -> Some $ inj $ Pair x y) <$> mkTerm vars <*> mkTerm vars))
--       ]
--
-- mkTerm :: [Some LispTerm] -> Gen (Some LispTerm)
-- mkTerm vars = frequency $
--   case vars of
--    [] -> closedConstructs
--    _  -> (4, elements vars) : closedConstructs
--   where
--     closedConstructs =
--       [ (10, Some . HFree <$> mkAtomTerm)
--       , (1,  ((\(Some x) (Some y) -> Some $ HFree $ inj $ Pair x y) <$> mkTerm vars <*> mkTerm vars))
--       ]
--
-- mkTermPair :: [Some LispTerm]
--            -> Gen (Some (LispTermF LispTerm :*: LispTermF LispTerm))
-- mkTermPair vars = frequency $
--   [ (10, Some <$> ((:*:) <$> mkAtomTerm <*> mkAtomTerm))
--   , (1, do
--       Some (x :*: y) <- mkTermPair vars
--       Some (z :*: w) <- mkTermPair vars
--       Some <$> ((:*:) <$> mkPairTerm [HFree x] [HFree z] <*> mkPairTerm [HFree y] [HFree w]) )
--   ]
--
-- chars :: [Char]
-- chars = ['a' .. 'z']
--
-- mkPred :: [Some LispTerm] -> Gen RPred
-- mkPred vars = -- TODO, Fit fresh in here somehow
--   oneof
--   [ Disconj <$> mkPred vars <*> mkPred vars
--   , Conj    <$> mkPred vars <*> mkPred vars
--   , (\(Some (x :*: y)) -> Eq (HFree x) (HFree y)) <$> mkTermPair vars
--   , (\(Some (x :*: y)) -> Neq (HFree x) (HFree y)) <$> mkTermPair vars
--   , elements [Success, Failure]
--   ]
--
-- two :: Applicative f => f a -> f (a, a)
-- two f = (,) <$> f <*> f
--
-- three :: Applicative f => f a -> f (a, a, a)
-- three f = (,,) <$> f <*> f <*> f
--
-- currentGoal :: Some LispTerm
-- currentGoal = Some $ HPure $ mkLVar 0 templateAtom
--
-- goals :: [Some LispTerm]
-- goals = [Some $ HPure $ mkLVar n templateAtom | n <- [1..10]]
--
-- forTerm :: Testable a => (Some (LispTermF LispTerm) -> a) -> Property
-- forTerm = forAll (mkTerm1 [currentGoal])
--
-- forTerm2 :: Testable a => (Some (LispTermF LispTerm :*: LispTermF LispTerm) -> a) -> Property
-- forTerm2 p = forAll (mkTermPair [currentGoal]) $ p
--
-- -- forTerm3 :: Testable a => (Some LispTerm -> Some LispTerm -> Some LispTerm -> a) -> Property
-- -- forTerm3 p = forAll (three $ mkTerm1 [currentGoal]) $ \(l, m, r) -> p l m r
--
-- forPred :: Testable a => (Predicate LispTermF -> a) -> Property
-- forPred = forAll (mkPred [currentGoal]) . (. toPredicate)
--
-- forPred2 :: Testable a => (Predicate LispTermF -> Predicate LispTermF -> a) -> Property
-- forPred2 p = forAll (two $ mkPred [currentGoal]) $
--              \(l, r) -> p (toPredicate l) (toPredicate r)
--
-- forPred3 :: Testable a => (Predicate LispTermF -> Predicate LispTermF -> Predicate LispTermF -> a) -> Property
-- forPred3 p = forAll (three $ mkPred [currentGoal]) $
--              \(l, m, r) -> p (toPredicate l) (toPredicate m) (toPredicate r)
