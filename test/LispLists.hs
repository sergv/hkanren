{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE EmptyDataDecls            #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

module LispLists where

import Control.Monad
import Data.HOrdering
import Data.HUtils
import Data.Monoid
import Data.Type.Equality
import Language.HKanren
-- import Test.QuickCheck hiding ((===), Success, Failure)

data Atom

instance (ix ~ Atom) => TypeI (AtomF h) ix where
  type SupportsIx (AtomF h) ix = Equal ix Atom
  data Type (AtomF h) idx where
    TAtom :: Type (AtomF h) Atom
  singType = TAtom

instance HEq (Type (AtomF h)) where
  heq TAtom TAtom = True

instance HEqHet (Type (AtomF h)) where
  heqIx TAtom TAtom = Just Refl

instance HOrd (Type (AtomF h)) where
  hcompare TAtom TAtom = EQ

instance HOrdHet (Type (AtomF h)) where
  hcompareIx TAtom TAtom = HEQ Refl


data AtomF :: (* -> *) -> (* -> *) where
  Atom :: String -> AtomF r Atom

iAtom :: (AtomF :<: h) => String -> h r Atom
iAtom = inj . Atom

instance (AtomF :<: h) => Unifiable AtomF h where
  unify (Atom x) (Atom y) s
    | x == y    = Just s
    | otherwise = Nothing

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

type family IsList (ix :: *) :: Bool where
  IsList (List ix) = 'True
  IsList b         = 'False

instance (TypeI h ix', List ix' ~ ix) => TypeI (ListF h) ix where
  type SupportsIx (ListF h) ix = IsList ix
  data Type (ListF h) idx where
    TList :: Type h ix' -> Type (ListF h) (List ix')
  singType = TList singType

instance (HEq (Type h)) => HEq (Type (ListF h)) where
  heq (TList x) (TList y) = heq x y

instance (HEqHet (Type h)) => HEqHet (Type (ListF h)) where
  heqIx (TList x) (TList y) =
    case heqIx x y of
      Just Refl -> Just Refl
      Nothing   -> Nothing

instance (HOrd (Type h)) => HOrd (Type (ListF h)) where
  hcompare (TList x) (TList y) = hcompare x y

instance (HOrdHet (Type h)) => HOrdHet (Type (ListF h)) where
  hcompareIx (TList x) (TList y) =
    case hcompareIx x y of
      HLT      -> HLT
      HEQ Refl -> HEQ Refl
      HGT      -> HGT



data ListF :: (* -> *) -> (* -> *) where
  Nil  :: (TypeI r ix) => ListF r (List ix)
  Cons :: (TypeI r ix) => r ix -> r (List ix) -> ListF r (List ix)

typeOfElems :: (TypeI f ix) => p f (List ix) -> Type f ix
typeOfElems _ = singType

instance (HFoldable h, HOrdHet (Type (h (Term h))), Unifiable h h) => Unifiable ListF h where
  unify Nil         Nil         = return
  unify (Cons x xs) (Cons y ys) =
    unifyTerms x y >=> unifyTerms xs ys
  unify _ _ = const Nothing

instance (HEq f) => HEq (ListF f) where
  heq Nil         Nil         = True
  heq (Cons x xs) (Cons y ys) = heq x y && heq xs ys
  heq _           _           = False

instance (HEqHet (Type f)) => HEqHet (ListF f) where
  heqIx :: forall ix ix'. ListF f ix -> ListF f ix' -> Maybe (ix :~: ix')
  heqIx x@Nil        y@Nil =
    case heqIx (typeOfElems x) (typeOfElems y) of
      Just Refl -> Just Refl
      Nothing   -> Nothing
  heqIx x@Nil        y@(Cons _ _) =
    case heqIx (typeOfElems x) (typeOfElems y) of
      Just Refl -> Just Refl
      Nothing   -> Nothing
  heqIx x@(Cons _ _) y@Nil =
    case heqIx (typeOfElems x) (typeOfElems y) of
      Just Refl -> Just Refl
      Nothing   -> Nothing
  heqIx x@(Cons _ _) y@(Cons _ _) =
    case heqIx (typeOfElems x) (typeOfElems y) of
      Just Refl -> Just Refl
      Nothing   -> Nothing

instance (HOrd f) => HOrd (ListF f) where
  hcompare Nil         Nil         = EQ
  hcompare Nil         (Cons _ _)  = LT
  hcompare (Cons _ _)  Nil         = GT
  hcompare (Cons x xs) (Cons y ys) = hcompare x y <> hcompare xs ys

instance (HOrdHet (Type f)) => HOrdHet (ListF f) where
  hcompareIx x@Nil        y@Nil        =
    case hcompareIx (typeOfElems x) (typeOfElems y) of
      HLT      -> HLT
      HEQ Refl -> HEQ Refl
      HGT      -> HGT
  hcompareIx x@Nil        y@(Cons _ _) =
    case hcompareIx (typeOfElems x) (typeOfElems y) of
      HLT      -> HLT
      HEQ Refl -> HEQ Refl
      HGT      -> HGT
  hcompareIx x@(Cons _ _) y@Nil        =
    case hcompareIx (typeOfElems x) (typeOfElems y) of
      HLT      -> HLT
      HEQ Refl -> HEQ Refl
      HGT      -> HGT
  hcompareIx x@(Cons _ _) y@(Cons _ _) =
    case hcompareIx (typeOfElems x) (typeOfElems y) of
      HLT      -> HLT
      HEQ Refl -> HEQ Refl
      HGT      -> HGT

instance HFunctorId ListF where
  hfmapId _ Nil         = Nil
  hfmapId f (Cons x xs) = Cons (f x) (f xs)

-- instance HFunctor ListF where
--   hfmap _ (Nil t)       = Nil t
--   hfmap f (Cons t x xs) = Cons t (f x) (f xs)

instance HFoldable ListF where
  hfoldMap _ Nil         = mempty
  hfoldMap f (Cons x xs) = f x <> f xs

instance (HShow f) => HShow (ListF f) where
  hshowsPrec _ Nil         = \xs -> "Nil" ++ xs
  hshowsPrec n (Cons x xs) =
    \ys -> showParen (n == 11) (\zs -> "Cons " ++ hshowsPrec 11 x (showChar ' ' $ hshowsPrec 11 xs zs)) ys


type LispTermF = ListF :+: AtomF
type LispTerm = Term LispTermF
-- type LispType = Type LispTermF

list :: (TypeI (LispTermF LispTerm) ix) => [LispTermF LispTerm ix] -> LispTermF LispTerm (List ix)
list = foldr (\x y -> inj $ Cons (HFree x) (HFree y)) (inj Nil)

ilist :: (TypeI (LispTermF LispTerm) ix) => [LispTermF LispTerm ix] -> LispTerm (List ix)
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
