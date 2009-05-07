------------------------------------------------------------------------
-- Finite sets defined in terms of Data.Star
------------------------------------------------------------------------

module Data.Star.Fin where

open import Data.Star
open import Data.Star.Nat as ℕ using (ℕ)
open import Data.Star.Pointer
open import Data.Unit

-- Finite sets are undecorated pointers into natural numbers.

Fin : ℕ → Set
Fin = Any (λ _ → ⊤) (λ _ → ⊤)

-- "Constructors".

zero : ∀ {n} → Fin (ℕ.suc n)
zero = this tt

suc : ∀ {n} → Fin n → Fin (ℕ.suc n)
suc = that tt
