{-# OPTIONS --level-universe #-}

open import Agda.Primitive

record ⊤ : Set where

bad : Setω
bad = (λ (ℓ : ⊤ → Level) → ∀ t → Set (ℓ t)) (λ _ → lzero)

-- Error:
--
-- funSort Set LevelUniv is not a valid sort
-- when checking that the expression ⊤ → Level is a type
