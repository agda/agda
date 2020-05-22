{-# OPTIONS --universe-polymorphism #-}
open import Common.Prelude
open import Common.Level
open import Common.Reflection

module UnquoteSetOmega where

`Level : Term
`Level = def (quote Level) []

-- building the syntax of ∀ ℓ → Set ℓ (of type Setω) is harmless
`∀ℓ→Setℓ : Term
`∀ℓ→Setℓ = pi (vArg `Level) (abs "_" (sort (set (var 0 []))))

-- unquoting it is now also fine (since we have sort Setω₁)
∀ℓ→Setℓ = unquote (give `∀ℓ→Setℓ)
