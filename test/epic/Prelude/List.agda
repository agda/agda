module Prelude.List where

open import Prelude.Bool
open import Prelude.Nat
open import Prelude.Fin

infixr 40 _::_

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL [] #-}
{-# BUILTIN CONS _::_ #-}

infixr 30 _++_

_++_ : {A : Set} -> List A -> List A -> List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys) 

snoc : {A : Set} -> List A -> A -> List A
snoc []        e = e :: []
snoc (x :: xs) e = x :: snoc xs e

length : {A : Set} -> List A -> Nat
length [] = 0
length (x :: xs) = 1 + length xs

zipWith : ∀ {A B C} -> (A -> B -> C) -> List A -> List B -> List C
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys
zipWith _ _ _ = []

map : ∀ {A B} -> (A -> B) -> List A -> List B
map _ []        = []
map f (x :: xs) = f x :: map f xs

mapIgen : ∀ {A B} -> (A -> B) -> List A -> List B
mapIgen = map

_!_ : ∀ {A} -> (xs : List A) -> Fin (length {A} xs) -> A
_!_ {A} (x :: xs) (fz .{length xs})   = x
_!_ {A} (x :: xs) (fs .{length xs} n) = _!_ {A} xs n
_!_ {A} [] ()

_[_]=_ : {A : Set} -> (xs : List A) -> Fin (length xs) -> A -> List A
(a :: as) [ fz ]= e = e :: as
(a :: as) [ fs n ]= e = a :: (as [ n ]= e)
[] [ () ]= e

listEq : {A : Set} -> (A -> A -> Bool) -> List A -> List A -> Bool
listEq _    []        [] = true
listEq _==_ (a :: as) (b :: bs) with a == b
... | true  = listEq _==_ as bs
... | false = false
listEq _ _ _ = false

tail : {A : Set} -> List A -> List A
tail [] = []
tail (x :: xs) = xs

reverse : {A : Set} -> List A -> List A
reverse [] = []
reverse (x :: xs) = reverse xs ++ (x :: [])

init : {A : Set} -> List A -> List A
init xs = reverse (tail (reverse xs))

filter : {A : Set} -> (A -> Bool) -> List A -> List A
filter p [] = []
filter p (a :: as) with p a
... | true  = a :: filter p as
... | false = filter p as
