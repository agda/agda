-- Tests bad inductive size preservation
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.BadInductiveSizePreservation where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

add : Nat → Nat → Nat
add zero y = y
add (suc x) y = suc (add x y)

foo : Nat → Nat
foo zero = zero
foo (suc n) = foo (add n (suc zero))
