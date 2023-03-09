{-# OPTIONS --cubical --safe --no-sized-types --no-guardedness #-}

module Agda.Builtin.Cubical.Glue where

open import Agda.Primitive
open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Equiv public

primitive
    primGlue    : ∀ {ℓ ℓ'} (A : Set ℓ) {φ : I}
      → (T : Partial φ (Set ℓ')) → (e : PartialP φ (λ o → T o ≃ A))
      → Set ℓ'
    prim^glue   : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
      → {T : Partial φ (Set ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
      → (t : PartialP φ T) → (a : A) → primGlue A T e
    prim^unglue : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
      → {T : Partial φ (Set ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
      → primGlue A T e → A
