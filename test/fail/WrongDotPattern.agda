
module WrongDotPattern where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data NonZero : Nat -> Set where
  nonZ : (n : Nat) -> NonZero (suc n)

f : (n : Nat) -> NonZero n -> Nat
f .zero (nonZ n) = n

