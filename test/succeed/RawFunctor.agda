{-# OPTIONS --universe-polymorphism #-}

module RawFunctor where

open import Common.Level

postulate RawFunctor : ∀ {ℓ} (F : Set ℓ → Set ℓ) → Set (lsuc ℓ)

-- Broken occurs check for levels made this not infer properly
postulate
  sequence⁻¹ : ∀ {F}{A} {P : A → Set} → RawFunctor F →
                 F (∀ i → P i) → ∀ i → F (P i)
