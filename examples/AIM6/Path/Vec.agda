
module Vec where

open import Star
open import Nat

data Step (A : Set) : Nat -> Nat -> Set where
  step : (x : A){n : Nat} -> Step A (suc n) n

Vec : (A : Set) -> Nat -> Set
Vec A n = Star (Step A) n zero

[] : {A : Set} -> Vec A zero
[] = ε

_::_ : {A : Set}{n : Nat} -> A -> Vec A n -> Vec A (suc n)
x :: xs = step x • xs

