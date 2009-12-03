------------------------------------------------------------------------
-- Injections
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Relation.Nullary.Injection where

open import Level
open import Relation.Binary
open import Relation.Binary.FunctionSetoid

Injective : ∀ {a₁ a₂ b₁ b₂} {A : Setoid a₁ a₂} {B : Setoid b₁ b₂} →
            A ⟶ B → Set _
Injective {A = A} {B} f = ∀ {x y} → f ⟨$⟩ x ≈₂ f ⟨$⟩ y → x ≈₁ y
  where
  open Setoid A renaming (_≈_ to _≈₁_)
  open Setoid B renaming (_≈_ to _≈₂_)

record Injection {f₁ f₂ t₁ t₂}
                 (From : Setoid f₁ f₂) (To : Setoid t₁ t₂) :
                 Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  field
    to        : From ⟶ To
    injective : Injective to
