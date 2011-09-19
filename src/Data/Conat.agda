------------------------------------------------------------------------
-- The Agda standard library
--
-- Coinductive "natural" numbers
------------------------------------------------------------------------

module Data.Conat where

open import Coinduction
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary

------------------------------------------------------------------------
-- The type

data Coℕ : Set where
  zero : Coℕ
  suc  : (n : ∞ Coℕ) → Coℕ

------------------------------------------------------------------------
-- Some operations

fromℕ : ℕ → Coℕ
fromℕ zero    = zero
fromℕ (suc n) = suc (♯ fromℕ n)

∞ℕ : Coℕ
∞ℕ = suc (♯ ∞ℕ)

infixl 6 _+_

_+_ : Coℕ → Coℕ → Coℕ
zero  + n = n
suc m + n = suc (♯ (♭ m + n))

------------------------------------------------------------------------
-- Equality

data _≈_ : Coℕ → Coℕ → Set where
  zero :                                 zero  ≈ zero
  suc  : ∀ {m n} (m≈n : ∞ (♭ m ≈ ♭ n)) → suc m ≈ suc n

setoid : Setoid _ _
setoid = record
  { Carrier       = Coℕ
  ; _≈_           = _≈_
  ; isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  }
  where
  refl : Reflexive _≈_
  refl {zero}  = zero
  refl {suc n} = suc (♯ refl)

  sym : Symmetric _≈_
  sym zero      = zero
  sym (suc m≈n) = suc (♯ sym (♭ m≈n))

  trans : Transitive _≈_
  trans zero      zero      = zero
  trans (suc m≈n) (suc n≈k) = suc (♯ trans (♭ m≈n) (♭ n≈k))
