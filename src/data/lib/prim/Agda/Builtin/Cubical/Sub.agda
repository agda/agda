{-# OPTIONS --cubical --safe --no-sized-types --no-guardedness
            --no-subtyping #-}

module Agda.Builtin.Cubical.Sub where

  open import Agda.Primitive.Cubical

  {-# BUILTIN SUB Sub #-}

  postulate
    inc : ∀ {ℓ} {A : Set ℓ} {φ} (x : A) → Sub A φ (λ _ → x)

  {-# BUILTIN SUBIN inc #-}

  primitive
    primSubOut : ∀ {ℓ} {A : Set ℓ} {φ : I} {u : Partial φ A} → Sub _ φ u → A
