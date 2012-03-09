module PatternSynonymOverapplied2 where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

pattern suc' x = suc x

f : Nat -> Nat
f zero       = zero
f (suc' m n) = n