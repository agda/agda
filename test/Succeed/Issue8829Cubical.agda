{-# OPTIONS --cubical --sized-types -WnoUnsupportedIndexedMatch #-}

-- Andreas, 2026-10-12, issue #8829
-- The domain IsOne φ of partial elements is finite,
-- so Partial φ (Nat i) is lower semi-continuous in i.

module Issue8829Cubical where

open import Agda.Primitive.Cubical
open import Agda.Builtin.Size
open import Agda.Builtin.Bool

data Nat : Size → Set where
  zero : ∀ {i} → Nat (↑ i)
  suc  : ∀ {i} → Nat i → Nat (↑ i)

postulate
  pass : ∀ {i} → Nat i → Nat i
  use  : ∀ {i j} {φ : I} → Partial φ (Nat i) → Partial φ (Nat j)

partial : ∀ {i} (φ : I) → Partial φ (Nat i) → Nat i → Bool
partial φ p zero    = true
partial φ p (suc n) = partial φ (use p) (pass n)
