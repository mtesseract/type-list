{-# LANGUAGE
      DataKinds
    , GADTs
    , PolyKinds
    , ScopedTypeVariables
    , TypeFamilies
    , TypeOperators
    , UndecidableInstances
    #-}

{-# OPTIONS_HADDOCK show-extensions #-}

{-| 
Module       : Data.Type.List
Description  : Operation on type-level lists and tuples.
Copyright    : (c) Marcin Mrotek, 2014
License      : BSD3
Maintainer   : marcin.jan.mrotek@gmail.com

Operations on type-level lists and tuples, together with their curried versions - the more apostrophes, the more arguments are missing from the function.
Curried type functions can be evaluated by the 'Apply' type family from "Data.Singletons".
-}

module Data.Type.List where

import GHC.TypeLits
import Data.Type.Bool
import Data.Type.Equality
import Data.Singletons

-- |Maps a curried type function over a type list.
type family Map (f :: TyFun a b -> *) (xs :: [a]) where
    Map f '[] = '[]
    Map f (x ': xs) = (Apply f x) ': xs

data Map'' :: TyFun (TyFun a b -> *) (TyFun [a] [b] -> *) -> * where
    Map'' :: Map'' f

data Map' :: (TyFun a b -> *) -> TyFun [a] [b] -> * where
    Map' :: Map' f g

type instance Apply Map'' f = Map' f
type instance Apply (Map' f) l = Map f l

type family Length xs where
    Length '[] = 0
    Length (x ': xs) = 1 + (Length xs)

data Length' :: TyFun [a] Nat -> * where
    Length' :: Length' l

type instance Apply Length' xs = Length xs

-- |Insert a type into a type list.
type family Insert a xs where
    Insert a '[]       = (a ': '[])
    Insert a (a ': xs) = (a ': xs)
    Insert a (x ': xs) = x ': (Insert a xs)

data Insert'' :: TyFun k (TyFun [k] [k] -> *) -> * where
    Insert'' :: Insert'' f

data Insert' :: k -> TyFun [k] [k] -> * where 
    Insert' :: Insert' x f

type instance Apply Insert'' x = Insert' x 
type instance Apply (Insert' x) xs = Insert x xs

-- |Set union over type lists.
type family Union xs ys where
    Union '[] ys = ys
    Union (x ': xs) ys = Insert x (Union xs ys)

data Union'' :: TyFun [k] (TyFun [k] [k] -> *) -> * where
    Union'' :: Union'' f

data Union' :: [k] -> TyFun [k] [k] -> * where
    Union' :: Union' xs f

type instance Apply Union'' xs = Union' xs
type instance Apply (Union' xs) ys = Union xs ys

-- |Remove a type from type list.
type family Remove x ys where
    Remove a '[] = '[]
    Remove a (a ': ys) = ys
    Remove a (y ': ys) = y ': (Remove a ys)

data Remove'' :: TyFun k (TyFun [k] [k] -> *) -> * where
    Remove'' :: Remove'' f

data Remove' :: k -> TyFun [k] [k] -> * where
    Remove' :: Remove' x f

type instance Apply Remove'' x = Remove' x
type instance Apply (Remove' x) xs = Remove x xs

type family Difference xs ys where
    Difference '[] ys = ys
    Difference (x ': xs) ys = Remove x (Difference xs ys)

data Difference'' :: TyFun [k] (TyFun [k] [k] -> *) -> * where
    Difference'' :: Difference'' f

data Difference' :: [k] -> TyFun [k] [k] -> * where
    Difference' :: Difference' xs f

type instance Apply Difference'' xs = Difference' xs
type instance Apply (Difference' xs) ys = Difference xs ys

type family ReverseAcc xs acc where
    ReverseAcc '[] acc = acc
    ReverseAcc (x ': xs) acc = ReverseAcc xs (x ': acc)

type family Reverse xs where
    Reverse xs = ReverseAcc xs '[]

data Reverse' :: TyFun [k] [k] -> * where
    Reverse' :: Reverse' f

type instance Apply Reverse' xs = Reverse xs

-- | Type list membership test.
type family Find x ys where
    Find x '[]       = False
    Find x (x ': ys) = True
    Find x (y ': ys) = Find x ys

data Find'' :: TyFun k (TyFun [k] Bool -> *) -> * where
    Find'' :: Find'' f

data Find' :: k -> TyFun [k] Bool -> * where
    Find' :: Find' x f

type instance Apply Find'' x = Find' x
type instance Apply (Find' x) xs = Find x xs

-- | Type list intersection. 
type family Intersection xs ys where
    Intersection '[] ys = '[]
    Intersection (x ': xs) (x ': ys) = x ': (Intersection xs ys)
    Intersection (x ': xs) (y ': ys) = If (Find x ys) (x ': (Intersection xs (y ': ys))) (Intersection xs (y ': ys))

data Intersection'' :: TyFun [k] (TyFun [k] [k] -> *) -> * where
    Intersection'' :: Intersection'' f

data Intersection' :: [k] -> TyFun [k] [k] -> * where
    Intersection' :: Intersection' xs f

type instance Apply Intersection'' xs = Intersection' xs
type instance Apply (Intersection' xs) ys = Intersection xs ys

-- |Test if two list do not contain any equal elements.
type family Distinct xs ys where
    Distinct '[] '[] = False
    Distinct (x ': xs) (x ': ys) = Distinct xs ys
    Distinct (x ': xs) (y ': ys) = Not (Find x (y ': ys)) && Distinct xs ys

data Distinct'' :: TyFun [k] (TyFun [k] Bool -> *) -> * where
    Distinct'' :: Distinct'' f

data Distinct' :: [k] -> TyFun [k] Bool -> * where
    Distinct' :: Distinct' xs f

type instance Apply Distinct'' xs = Distinct' xs
type instance Apply (Distinct' xs) ys = Distinct xs ys

-- |Lookup an association type list.
type family Lookup (x :: k) (l :: [(k,a)]) where
    Lookup k ('(k,a) ': ls) = a
    Lookup k ('(x,a) ': ls) = Lookup k ls

data Lookup'' :: TyFun k (TyFun [(k,a)] a -> *) -> * where
    Lookup'' :: Lookup'' f

data Lookup' :: k -> TyFun [(k,a)] a -> * where
    Lookup' :: Lookup' x f

type instance Apply Lookup'' x = Lookup' x
type instance Apply (Lookup' x) xs = Lookup x xs

-- |First element of a type pair.
type family Fst k where
    Fst '(a,b) = a

data Fst' :: TyFun (a,b) a -> * where
    Fst' :: Fst' f
type instance Apply Fst' '(a, b) = a

-- |Second element of a type pair.
type family Snd k where
    Snd '(a,b) = b

data Snd' :: TyFun (a,b) b -> * where
    Snd' :: Snd' k

type instance Apply Snd' '(a, b) = b

-- |Cons a type pair with elements in order.
type family AsFst a b where
    AsFst a b = '(a,b)

data AsFst'' :: TyFun a (TyFun b (a,b) -> *) -> * where
    AsFst'' :: AsFst'' f

data AsFst' :: a -> TyFun b (a,b) -> * where
    AsFst' :: AsFst' a f

type instance Apply AsFst'' a = AsFst' a
type instance Apply (AsFst' a) b = AsFst a b

-- |Cons a type pair in reverse order.
type family AsSnd a b where
    AsSnd a b = '(b,a)

data AsSnd'' :: TyFun a (TyFun b (b,a) -> *) -> * where
    AsSnd'' :: AsSnd'' f

data AsSnd' :: a -> TyFun b (b,a) -> * where
    AsSnd' :: AsSnd' k f

type instance Apply AsSnd'' a = AsSnd' a
type instance Apply (AsSnd' a) b = AsSnd a b

-- |Swap elements of a type pair.
type family Swap k where
    Swap '(a,b) = '(b,a)

data Swap' :: TyFun (a,b) (b,a) -> * where
    Swap' :: Swap' f

type instance Apply Swap' '(a,b) = Swap '(a,b)


