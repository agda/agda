
module Lib.List where

infixr 40 _::_ _++_

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

_++_ : {A : Set} -> List A -> List A -> List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

foldr : {A B : Set} -> (A -> B -> B) -> B -> List A -> B
foldr f z [] = z
foldr f z (x :: xs) = f x (foldr f z xs)

map : {A B : Set} -> (A -> B) -> List A -> List B
map f [] = []
map f (x :: xs) = f x :: map f xs