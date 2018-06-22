{-# OPTIONS --cubical #-}
module Agda.Builtin.Cubical.Id where

  open import Agda.Primitive.Cubical
  open import Agda.Builtin.Cubical.Path

  postulate
    Id : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ

  {-# BUILTIN ID           Id       #-}
  {-# BUILTIN CONID        conid    #-}

  primitive
    primDepIMin : _
    primIdFace : ∀ {ℓ} {A : Set ℓ} {x y : A} → Id x y → I
    primIdPath : ∀ {ℓ} {A : Set ℓ} {x y : A} → Id x y → x ≡ y

  primitive
    primIdJ : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : ∀ y → Id x y → Set ℓ') →
                P x (conid i1 (λ i → x)) → ∀ {y} (p : Id x y) → P y p
