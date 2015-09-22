
-- Occurs check when unifying indices in patterns
module OccursCheck where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

f : {n : Nat} -> n == suc n -> Nat
f refl = zero

