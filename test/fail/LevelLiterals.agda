-- There are no level literals in the concrete syntax. This file tests
-- if type errors use level literals.

module LevelLiterals where

open import Common.Level

data ⊥ : Set₁ where

DoubleNegated : ∀ {ℓ} → Set ℓ → Set
DoubleNegated A = (A → ⊥) → ⊥
