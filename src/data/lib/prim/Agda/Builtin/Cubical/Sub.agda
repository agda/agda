{-# OPTIONS --erased-cubical --safe --no-sized-types --no-guardedness #-}

module Agda.Builtin.Cubical.Sub where

  open import Agda.Primitive.Cubical

  {-# BUILTIN SUB Sub #-}

  postulate
    inS : ∀ {ℓ} {A : Set ℓ} {φ} (x : A) → Sub A φ (λ _ → x)

  {-# BUILTIN SUBIN inS #-}

  -- Sub A φ u is treated as A.
  {-# COMPILE JS inS = _ => _ => _ => x => x #-}

  primitive
    primSubOut : ∀ {ℓ} {A : Set ℓ} {φ : I} {u : Partial φ A} → Sub _ φ u → A
