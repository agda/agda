-- Andreas, 2013-10-27

{-# OPTIONS --copatterns #-}

module Issue907a where

import Common.Level
open import Common.Prelude
open import Common.Product

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero

test : ∀ {A} → Σ Nat λ n → Vec A n
proj₁ test = zero
proj₂ test = []
