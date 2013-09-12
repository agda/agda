
-- module Basic where

data List (A : Set) : Set

data List A where
  nil : List A
  cons : A -> List A -> List A

append : {A : Set} -> List A -> List A -> List A
append nil ys = ys
append (cons x xs) ys = cons x (append xs ys)

record Equiv {A : Set} (R : A -> A -> Set) : Set
record Equiv {A} R where
  constructor equiv
  field
    ref : (x : A) -> R x x
    sym : (x : A) -> (y : A) -> R x y -> R y x
    trans : (x y z : A) -> R x y -> R y z -> R x z

open Equiv

