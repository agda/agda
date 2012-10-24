
module DifferentArities where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

f : Nat -> Nat -> Nat
f zero      = \x -> x
f (suc n) m = f n (suc m)

