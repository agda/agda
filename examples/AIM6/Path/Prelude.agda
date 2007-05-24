
module Prelude where

id : {A : Set} -> A -> A
id x = x

_·_ : {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
f · g = \ x -> f (g x)

Rel : Set -> Set1
Rel X = X -> X -> Set

record True : Set where

! : {A : Set} -> A -> True
! = _


