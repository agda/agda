------------------------------------------------------------------------
-- Left inverses
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Relation.Nullary.LeftInverse where

open import Level
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary
open import Relation.Binary.FunctionSetoid
open import Relation.Nullary.Injection

_LeftInverseOf_ : ∀ {a₁ a₂ b₁ b₂} {A : Setoid a₁ a₂} {B : Setoid b₁ b₂} →
                  B ⟶ A → A ⟶ B → Set _
_LeftInverseOf_ {A = A} f g = ∀ x → f ⟨$⟩ (g ⟨$⟩ x) ≈₁ x
  where open Setoid A renaming (_≈_ to _≈₁_)

record LeftInverse {f₁ f₂ t₁ t₂}
                   (From : Setoid f₁ f₂) (To : Setoid t₁ t₂) :
                   Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  field
    to           : From ⟶ To
    from         : To ⟶ From
    left-inverse : from LeftInverseOf to

  open Setoid      From
  open EqReasoning From

  injective : Injective to
  injective {x} {y} eq = begin
    x                    ≈⟨ sym (left-inverse x) ⟩
    from ⟨$⟩ (to ⟨$⟩ x)  ≈⟨ cong from eq ⟩
    from ⟨$⟩ (to ⟨$⟩ y)  ≈⟨ left-inverse y ⟩
    y                    ∎

  injection : Injection From To
  injection = record { to = to; injective = injective }
