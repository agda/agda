-- There are no level literals in the concrete syntax. This file tests
-- if type errors use level literals.

{-# OPTIONS --universe-polymorphism #-}

module LevelLiterals where

open import Imports.Level

data ⊥ : Set₁ where

DoubleNegated : ∀ {ℓ} → Set ℓ → Set
DoubleNegated A = (A → ⊥) → ⊥
