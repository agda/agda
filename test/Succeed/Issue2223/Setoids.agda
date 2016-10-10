-- Andreas, 2016-10-09, re issue #2223

module Issue2223.Setoids where

open import Common.Level

record Setoid c ℓ : Set (lsuc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier       : Set c
    _≈_           : (x y : Carrier) → Set ℓ

_⟨_⟩_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
        A → (A → B → C) → B → C
x ⟨ f ⟩ y = f x y
