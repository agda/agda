------------------------------------------------------------------------
-- Empty type
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Data.Empty where

open import Level

data ⊥ : Set where

⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ → Whatever
⊥-elim ()
