
module Data.List where

import Prelude
import Data.Nat

open Prelude
open Data.Nat

infixr 50 _::_

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

length : {A : Set} -> List A -> Nat
length []        = 0
length (_ :: xs) = 1 + length xs

map : {A, B : Set} -> (A -> B) -> List A -> List B
map f []        = []
map f (x :: xs) = f x :: map f xs

zipWith : {A, B, C : Set} -> (A -> B -> C) -> List A -> List B -> List C
zipWith f []        []        = []
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys
zipWith f []        (_ :: _)  = []
zipWith f (_ :: _)  []        = []

foldr : {A, B : Set} -> (A -> B -> B) -> B -> List A -> B
foldr f z []        = z
foldr f z (x :: xs) = f x (foldr f z xs)

replicate : {A : Set} -> Nat -> A -> List A
replicate  zero   x = []
replicate (suc n) x = x :: replicate n x

iterate : {A : Set} -> Nat -> (A -> A) -> A -> List A
iterate  zero   f x = []
iterate (suc n) f x = x :: iterate n f (f x)

splitAt : {A : Set} -> Nat -> List A -> List A × List A
splitAt  zero   xs        = < [] | xs >
splitAt (suc n) []        = < [] | [] >
splitAt (suc n) (x :: xs) = add x $ splitAt n xs
  where
    add : _ -> List _ × List _ -> List _ × List _
    add x < ys | zs > = < x :: ys | zs >

