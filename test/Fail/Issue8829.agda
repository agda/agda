{-# OPTIONS --sized-types #-}

-- Andreas, 2026-10-12, issue #8829
-- Missing semi-continuity check for successor-style sized types
-- lets us prove False.

open import Agda.Builtin.Size
open import Agda.Builtin.Nat

data ⊥ : Set where

-- IsNat i n is inhabited iff n < i.

data IsNat : Size → Nat → Set where
  isZero : ∀ i     →             IsNat (↑ i) zero
  isSuc  : ∀ i {n} → IsNat i n → IsNat (↑ i) (suc n)

T : Size → Set
T i = ∀ n → IsNat i n

shift : ∀ i → T (↑ i) → T i
shift i f n with f (suc n)
... | isSuc j b = b

-- T i = ∀ n → IsNat i n is false for all finite i but inhabited at ω (see allIsNat):
-- not lower semi-continuous in i.
loop : ∀ i → T i → ⊥
loop i f = aux (f zero)
  where
  aux : IsNat i zero → ⊥
  aux (isZero j) = loop j (shift j f)

allIsNat : T ∞
allIsNat zero    = isZero ∞
allIsNat (suc n) = isSuc ∞ (allIsNat n)

absurd : ⊥
absurd = loop ∞ allIsNat
