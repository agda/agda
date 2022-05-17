-- Andreas, 2015-05-28 example by Andrea Vezzosi

{-# OPTIONS --sized-types #-}

open import Common.Size

data Nat (i : Size) : Set where
  zero : ∀ (j : Size< i) → Nat i
  suc  : ∀ (j : Size< i) → Nat j → Nat i

{-# TERMINATING #-}
-- This definition is fine, the termination checker is too strict at the moment.
fix : ∀ {C : Size → Set} → (∀ i → (∀ (j : Size< i) → Nat j -> C j) → Nat i → C i) → ∀ i → Nat i → C i
fix t i (zero j)  = t i (λ (j : Size< i) → fix t j) (zero j)
fix t i (suc j n) = t i (λ (j : Size< i) → fix t j) (suc j n)

case : ∀ i {C : Set} (n : Nat i) (z : C) (s : ∀ (j : Size< i) → Nat j → C) → C
case i (zero j)  z s = z
case i (suc j n) z s = s j n

applyfix : ∀ {C : Size → Set} i (n : Nat i)
  → (∀ i → (∀ (j : Size< i) → Nat j -> C j) → Nat i → C i)
  → C i
applyfix i n f = fix f i n

module M (i0 : Size) (bot : ∀{i} → Nat i) (A : Set) (default : A) where

  loops : A
  loops = applyfix (↑ i0) (zero i0) λ i r (_ : Nat i) →
      case i bot default λ (j : Size< i) (n : Nat j) →   -- Size< i is possibly empty, should be rejected
      case j n   default λ (h : Size< j) (_ : Nat h) →
      r (↑ h) (zero h)

  -- loops
  -- --> fix t (↑ i0) (zero i0)
  -- --> t (↑ i0) (fix t) (zero i0)
  -- --> case i0 bot default λ j n → case j n default λ h _ → fix t (↑ h) (zero h)
  -- and we have reproduced (modulo [h/i0]) what we started with

  -- The above needs this inference to typecheck
  -- h < j,   j < i
  -- ---------------------
  -- ↑ h < i
