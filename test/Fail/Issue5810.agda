{-# OPTIONS --level-universe #-}

open import Agda.Primitive

record ⊤ : Set where

bad : Setω
bad = (λ (ℓ : ⊤ → Level) → ∀ t → Set (ℓ t)) (λ _ → lzero)
