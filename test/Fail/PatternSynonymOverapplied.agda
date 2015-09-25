module PatternSynonymOverapplied where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

pattern suc' x = suc x

f : Nat -> Nat
f n = suc' n n
