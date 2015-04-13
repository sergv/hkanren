----------------------------------------------------------------------------
-- |
-- Module      :  Language.DSKanren.Subst
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverlappingInstances      #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

module Language.HKanren.Subst
  ( Subst
  , extend
  , lookup
  , lookupVar
  -- , delete -- TODO
  , domain
  , empty
  , LVar
  , mkLVar
  , mkLVarType
  -- , suc
  -- , suc'
  , Term
  , ClosedTerm
  , Type
  , FunctorOf
  , TypeRep(..)
  )
where

import Control.Applicative hiding (empty)
import Data.HMap (HMap)
import qualified Data.HMap as HM
import Data.HOrdering
import Data.HUtils
import Data.Monoid
import Data.Type.Equality

import Prelude hiding (lookup)

type ClosedTerm h = HFix h
type Type t = ClosedTerm (TypeOf t)
type Term h = HFree h (LVar h)

type family FunctorOf (f :: * -> *) :: (* -> *) -> (* -> *) where
  FunctorOf (HFree f ix) = f

-- todo: make TypeRep operate over types of kind (* -> *) in order to remove
-- "FunctorOf" hack and be able to define HFunctor instance for ListF.
class TypeRep (f :: (* -> *) -> (* -> *)) where
  data TypeOf f :: (* -> *) -> (* -> *)
  typeOf :: f r ix -> TypeOf f (Type (FunctorOf r)) ix

instance (TypeRep f, TypeRep g) => TypeRep (f :+: g) where
  data TypeOf (f :+: g) r ix =
      TInl (TypeOf f r ix)
    | TInr (TypeOf g r ix)
  typeOf (Inl x) = TInl $ typeOf x
  typeOf (Inr y) = TInr $ typeOf y

instance (HShow (TypeOf f e), HShow (TypeOf g e)) => HShow (TypeOf (f :+: g) e) where
  hshowsPrec n (TInl x) = \xs -> showParen (n == 11) (\ys -> "TInl " ++ hshowsPrec 11 x ys) xs
  hshowsPrec n (TInr y) = \xs -> showParen (n == 11) (\ys -> "TInr " ++ hshowsPrec 11 y ys) xs


instance (HEq (TypeOf f e), HEq (TypeOf g e)) => HEq (TypeOf (f :+: g) e) where
  heq (TInl x) (TInl y) = heq x y
  heq (TInr x) (TInr y) = heq x y
  heq _        _        = False

instance (HEqHet (TypeOf f e), HEqHet (TypeOf g e)) => HEqHet (TypeOf (f :+: g) e) where
  heqIx (TInl x) (TInl y) = heqIx x y
  heqIx (TInr x) (TInr y) = heqIx x y
  heqIx _        _        = Nothing

instance (HOrd (TypeOf f e), HOrd (TypeOf g e)) => HOrd (TypeOf (f :+: g) e) where
  hcompare (TInl x) (TInl y) = hcompare x y
  hcompare (TInr x) (TInr y) = hcompare x y
  hcompare (TInl _) (TInr _) = LT
  hcompare (TInr _) (TInl _) = GT

instance (HOrdHet (TypeOf f e), HOrdHet (TypeOf g e)) => HOrdHet (TypeOf (f :+: g) e) where
  hcompareIx (TInl x) (TInl y) = hcompareIx x y
  hcompareIx (TInr x) (TInr y) = hcompareIx x y
  hcompareIx (TInl _) (TInr _) = HLT
  hcompareIx (TInr _) (TInl _) = HGT


instance (HFunctorId (TypeOf f), HFunctorId (TypeOf g)) => HFunctorId (TypeOf (f :+: g)) where
  hfmapId f (TInl x) = TInl $ hfmapId f x
  hfmapId f (TInr y) = TInr $ hfmapId f y

instance (HFunctor (TypeOf f), HFunctor (TypeOf g)) => HFunctor (TypeOf (f :+: g)) where
  hfmap f (TInl x) = TInl $ hfmap f x
  hfmap f (TInr y) = TInr $ hfmap f y

instance (HFoldable (TypeOf f), HFoldable (TypeOf g)) => HFoldable (TypeOf (f :+: g)) where
  hfoldMap f (TInl x) = hfoldMap f x
  hfoldMap f (TInr y) = hfoldMap f y

instance (HTraversable (TypeOf f), HTraversable (TypeOf g)) => HTraversable (TypeOf (f :+: g)) where
  htraverse f (TInl x) = TInl <$> htraverse f x
  htraverse f (TInr y) = TInr <$> htraverse f y


instance {-# OVERLAPS #-} TypeOf f :<: TypeOf (f :+: g) where
  inj = TInl
  proj (TInl x) = Just x
  proj _        = Nothing

instance {-# OVERLAPS #-} (TypeOf f :<: TypeOf g) => TypeOf f :<: TypeOf (h :+: g) where
  inj = TInr . inj
  proj (TInr x) = proj x
  proj _        = Nothing


-- class TypeRep (f :: (* -> *) -> (* -> *)) (h :: (* -> *) -> (* -> *)) | f -> h where
--   type TypeOf f :: (* -> *) -> (* -> *)
--   typeOf :: f r ix -> (TypeOf f) (Type h) ix
--
-- instance forall f g h. (TypeRep f h, TypeRep g h) => TypeRep (f :+: g) h where
--   type TypeOf (f :+: g) = TypeOf f :+: TypeOf g
--   -- typeOf :: forall r ix. (f :+: g) r ix -> (TypeOf (f :+: g)) (Type h) ix
--   typeOf (Inl x) = Inl $ typeOf x -- hcata (HFix . inj) $ typeOf x
--   typeOf (Inr y) = Inr $ typeOf y -- hcata (HFix . inj) $ typeOf y

-- instance forall f g h.
--          ( TypeRep f h, HFunctor (TypeOf f)
--          , TypeRep g h, HFunctor (TypeOf g)
--          , f :<: (f :+: g), g :<: (f :+: g)
--          ) => TypeRep (f :+: g) h where
--   type TypeOf (f :+: g) = TypeOf f :+: TypeOf g
--   typeOf :: forall r ix. (f :+: g) r ix -> TypeOf (f :+: g) (Type h) ix
--   typeOf (Inl x) = Inl $ (typeOf x :: TypeOf f (Type h) ix) -- hcata (HFix . inj) $ typeOf x
--   typeOf (Inr y) = undefined -- hcata (HFix . inj) $ typeOf y

-- | Logic variable.
data LVar (f :: (* -> *) -> (* -> *)) ix where
  LVar :: Integer -> Type f ix -> LVar f ix
  -- deriving (Show, Eq, Ord)

instance (HEq (Type h)) => HEq (LVar h) where
  heq (LVar n x) (LVar m y) = n == m && heq x y

instance (HOrdHet (Type h)) => HEqHet (LVar h) where
  heqIx (LVar _ x) (LVar _ y) =
    case heqIx x y of
      Just Refl -> Just Refl
      Nothing   -> Nothing

instance (HOrd (Type h)) => HOrd (LVar h) where
  hcompare (LVar n x) (LVar m y) = compare n m <> hcompare x y

instance (HOrdHet (Type h)) => HOrdHet (LVar h) where
  hcompareIx (LVar _ x) (LVar _ y) = hcompareIx x y

instance HShow (LVar f) where
  hshowsPrec n (LVar m _) = \xs -> showParen (n == 11) (\ys -> "LVar " ++ show m ++ ys) xs

-- suc :: LVar h ix -> LVar h ix
-- suc (LVar n x) = LVar (n + 1) x
--
-- suc' :: (HFunctor h) => LVar h ix -> h f ix' -> LVar h ix'
-- suc' (LVar n _) y = LVar (n + 1) $ hfmap (const $ K ()) y

mkLVar :: (TypeRep h) => Integer -> Term h ix -> LVar h ix
mkLVar n (HPure (LVar _ t)) = LVar n t
mkLVar n (HFree x)          = LVar n $ HFix $ typeOf x

mkLVarType :: (TypeRep h) => Integer -> Type h ix -> LVar h ix
mkLVarType n t = LVar n t

newtype Subst h = Subst (HMap (LVar h) (Term h))

lookup :: (HOrdHet (Type h)) => LVar h ix -> Subst h -> Maybe (Term h ix)
lookup k (Subst s) = HM.lookup k s

lookupVar :: Integer -> Subst h -> Maybe (Some (Term h))
lookupVar n (Subst s) = HM.lookupWith (\(LVar m _) -> compare n m) s

extend :: (HOrdHet (Type h)) => LVar h ix -> Term h ix -> Subst h -> Subst h
extend k v (Subst s) = Subst $ HM.insert k v s

domain :: Subst h -> [Some (LVar h)]
domain (Subst s) = HM.keys s

empty :: Subst t
empty = Subst HM.empty

