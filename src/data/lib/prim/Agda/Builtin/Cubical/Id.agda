{-# OPTIONS --erased-cubical --safe --no-sized-types --no-guardedness #-}

module Agda.Builtin.Cubical.Id where

  open import Agda.Primitive.Cubical
  open import Agda.Builtin.Cubical.Path
  open import Agda.Builtin.Cubical.Sub renaming (primSubOut to ouc; Sub to _[_↦_])

  {-# BUILTIN ID           Id       #-}
  {-# BUILTIN REFLID       reflId   #-}

  private
    module ConId where
      primitive
        primConId : ∀ {ℓ} {A : Set ℓ} {x y : A} → I → x ≡ y → Id x y

  open ConId public renaming (primConId to conid)

  -- Id x y is treated as a pair of I and x ≡ y, using "i" for the
  -- first component and "p" for the second.
  {-# COMPILE JS conid =
      _ => _ => _ => _ => i => p => { return { "i" : i, "p" : p } }
    #-}

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
