------------------------------------------------------------------------
-- Coinductive "natural" numbers
------------------------------------------------------------------------

module Data.Conat where

open import Coinduction
open import Data.Nat using (ℕ; zero; suc)

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
