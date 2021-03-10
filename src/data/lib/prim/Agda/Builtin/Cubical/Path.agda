{-# OPTIONS --cubical --safe --no-sized-types --no-guardedness
            --no-subtyping #-}

module Agda.Builtin.Cubical.Path where

  open import Agda.Primitive.Cubical

  postulate
    PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ

  {-# BUILTIN PATHP        PathP     #-}

  infix 4 _≡_

  -- We have a variable name in `(λ i → A)` as a hint for case
  -- splitting.
  _≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
  _≡_ {A = A} = PathP (λ i → A)

  {-# BUILTIN PATH         _≡_     #-}
