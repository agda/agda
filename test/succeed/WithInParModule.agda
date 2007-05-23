module WithInParModule (A : Set) where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Bool : Set where
  true : Bool
  false : Bool

isZero : Nat -> Bool
isZero zero = true
isZero (suc _) = false


f : Nat -> Nat
f n with isZero n
f n | true = zero
f n | false = suc zero

g : Nat -> Nat
g zero = zero
g (suc n) with g n
g (suc n) | zero = n

