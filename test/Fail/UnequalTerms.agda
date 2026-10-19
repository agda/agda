module UnequalTerms where

open import Agda.Builtin.Nat

data IsZero : Nat → Set where
  zero : IsZero 0

err1 : IsZero 1
err1 = zero
