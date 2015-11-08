-- Andreas, 2015-05-28 example by Andrea Vezzosi

open import Common.Size

data Nat (i : Size) : Set where
  zero : ∀ {j : Size< i} → Nat i
  suc  : ∀ {j : Size< i} → Nat j → Nat i

{-# TERMINATING #-}
-- This definition is fine, the termination checker is too strict at the moment.
fix : ∀ {C : Size → Set}
  → (∀{i} → (∀ {j : Size< i} → Nat j -> C j) → Nat i → C i)
  → ∀{i} → Nat i → C i
fix t zero    = t (fix t) zero
fix t (suc n) = t (fix t) (suc n)

case : ∀ {i} {C : Set} (n : Nat i) (z : C) (s : ∀ {j : Size< i} → Nat j → C) → C
case zero    z s = z
case (suc n) z s = s n

applyfix : ∀ {C : Size → Set} {i} (n : Nat i)
  → (∀{i} → (∀ {j : Size< i} → Nat j -> C j) → Nat i → C i)
  → C i
applyfix n f = fix f n

module M (i0 : Size) (bot : ∀{i} → Nat i) (A : Set) (default : A) where

  -- Fine with extended lambda
  ok : A
  ok = applyfix (zero {i = ↑ i0}) λ {i} r _ →
      case {i} bot default λ{ {j} n →
      case {j} n   default λ{ {k} _ →
      r (zero {j = k}) }}

  -- ok
  -- --> fix t zero
  -- --> t (fix t) zero
  -- --> case bot default (aux i r _)
