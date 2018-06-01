{-# OPTIONS --omega-in-omega #-}

open import Agda.Primitive

test : Setω
test = Setω

record R : Setω where
  field
     A : ∀ {ℓ} → Set ℓ

data Type : Setω where
  el : ∀ {ℓ} → Set ℓ → Type
