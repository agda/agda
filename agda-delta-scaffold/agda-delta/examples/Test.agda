module Test where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

plus : Nat → Nat → Nat
plus zero n = n
plus (suc m) n = suc (plus m n)
