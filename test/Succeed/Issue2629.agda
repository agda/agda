{-# OPTIONS --exact-split #-}

open import Agda.Builtin.Nat

data IsZero : Nat → Set where
  isZero : IsZero 0

test : (n m : Nat) → IsZero n → IsZero m → Nat
test zero zero _ _ = zero
test (suc _) _ () _
test _ (suc _) _ ()
