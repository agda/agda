
module Data.List where

import Prelude
import Data.Nat
import Data.Tuple

open Prelude
open Data.Nat
open Data.Tuple

infixr 50 _::_ _++_

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _::_ #-}

length : {A : Set} -> List A -> Nat
length []        = 0
length (_ :: xs) = 1 + length xs

map : {A B : Set} -> (A -> B) -> List A -> List B
map f []        = []
map f (x :: xs) = f x :: map f xs

_++_ : {A : Set} -> List A -> List A -> List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

zipWith : {A B C : Set} -> (A -> B -> C) -> List A -> List B -> List C
zipWith f []        []        = []
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys
zipWith f []        (_ :: _)  = []
zipWith f (_ :: _)  []        = []

foldr : {A B : Set} -> (A -> B -> B) -> B -> List A -> B
foldr f z []        = z
foldr f z (x :: xs) = f x (foldr f z xs)

foldl : {A B : Set} -> (B -> A -> B) -> B -> List A -> B
foldl f z []        = z
foldl f z (x :: xs) = foldl f (f z x) xs

replicate : {A : Set} -> Nat -> A -> List A
replicate  zero   x = []
replicate (suc n) x = x :: replicate n x

iterate : {A : Set} -> Nat -> (A -> A) -> A -> List A
iterate  zero   f x = []
iterate (suc n) f x = x :: iterate n f (f x)

splitAt : {A : Set} -> Nat -> List A -> List A × List A
splitAt  zero   xs        = < [] , xs >
splitAt (suc n) []        = < [] , [] >
splitAt (suc n) (x :: xs) = add x $ splitAt n xs
  where
    add : _ -> List _ × List _ -> List _ × List _
    add x < ys , zs > = < x :: ys , zs >

reverse : {A : Set} -> List A -> List A
reverse xs = foldl (flip _::_) [] xs

