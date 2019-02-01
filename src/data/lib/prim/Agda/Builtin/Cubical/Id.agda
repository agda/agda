{-# OPTIONS --cubical --safe --no-sized-types --no-guardedness #-}
module Agda.Builtin.Cubical.Id where

  open import Agda.Primitive.Cubical
  open import Agda.Builtin.Cubical.Path
  open import Agda.Builtin.Cubical.Sub renaming (primSubOut to ouc; Sub to _[_↦_])

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


  primitive
    primIdElim : ∀ {a c} {A : Set a} {x : A}
                   (C : (y : A) → Id x y → Set c) →
                   ((φ : I) (y : A [ φ ↦ (λ _ → x) ])
                    (w : (x ≡ ouc y) [ φ ↦ (λ { (φ = i1) → \ _ → x}) ]) →
                    C (ouc y) (conid φ (ouc w))) →
                   {y : A} (p : Id x y) → C y p
