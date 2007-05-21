
module WrongNumberOfConstructorArguments where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

f : Nat -> Nat
f (zero n) = n
f suc      = zero

