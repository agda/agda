{-# OPTIONS --cubical --no-sized-types --no-guardedness #-}
module Agda.Builtin.Cubical.Path where

  open import Agda.Primitive.Cubical

  postulate
    PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ

  {-# BUILTIN PATHP        PathP     #-}

  infix 4 _≡_
  _≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
  _≡_ {A = A} = PathP (λ _ → A)

  {-# BUILTIN PATH         _≡_     #-}
