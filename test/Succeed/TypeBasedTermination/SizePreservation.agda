-- Tests a trivial usage of size preservation
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}

module TypeBasedTermination.SizePreservation where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

idn : Nat → Nat
idn zero = zero
idn (suc n) = idn n

foo : Nat → Nat
foo zero = zero
foo (suc n) = foo (idn n)
