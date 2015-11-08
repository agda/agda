{-# OPTIONS --universe-polymorphism #-}

-- It's possible to compute levels
module ComputedLevels where

open import Common.Level

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

N-ary-level : Level → Level → ℕ → Level
N-ary-level ℓ₁ ℓ₂ zero    = ℓ₂
N-ary-level ℓ₁ ℓ₂ (suc n) = ℓ₁ ⊔ N-ary-level ℓ₁ ℓ₂ n

N-ary : ∀ {ℓ₁ ℓ₂} (n : ℕ) → Set ℓ₁ → Set ℓ₂ → Set (N-ary-level ℓ₁ ℓ₂ n)
N-ary zero    A B = B
N-ary (suc n) A B = A → N-ary n A B

