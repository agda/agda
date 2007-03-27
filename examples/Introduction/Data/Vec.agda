
-- When defining types by recursion it is sometimes difficult to infer implicit
-- arguments. This module illustrates the problem and shows how to get around
-- it.

module Introduction.Data.Vec where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Nil : Set where
  nil' : Nil

data Cons (A As : Set) : Set where
  _::'_ : A -> As -> Cons A As

mutual
  Vec' : Set -> Nat -> Set
  Vec' A  zero   = Nil
  Vec' A (suc n) = Cons A (Vec A n)

  data Vec (A : Set)(n : Nat) : Set where
    vec : Vec' A n -> Vec A n

nil : {A : Set} -> Vec A zero
nil = vec nil'

_::_ : {A : Set}{n : Nat} -> A -> Vec A n -> Vec A (suc n)
x :: xs = vec (x ::' xs)

map : {n : Nat}{A B : Set} -> (A -> B) -> Vec A n -> Vec B n
map {zero}  f (vec nil')       = nil
map {suc n} f (vec (x ::' xs)) = f x :: map f xs

