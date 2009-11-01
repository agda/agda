------------------------------------------------------------------------
-- Empty type
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Data.Empty where

open import Level

data ⊥ : Set where

⊥-elim : ∀ {ℓ} {Whatever : Set ℓ} → ⊥ → Whatever
⊥-elim ()
