
module IlltypedPattern where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

f : (A : Set) -> A -> A
f A zero = zero

