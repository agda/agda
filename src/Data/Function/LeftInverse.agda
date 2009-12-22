------------------------------------------------------------------------
-- Left inverses
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Data.Function.LeftInverse where

open import Data.Product
open import Level
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary
open import Data.Function.Equality as F
  using (_⟶_; _⇨_; _⟨$⟩_) renaming (_∘_ to _⟪∘⟫_)
open import Data.Function.Injection using (Injective; Injection)

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
    from ⟨$⟩ (to ⟨$⟩ x)  ≈⟨ F.cong from eq ⟩
    from ⟨$⟩ (to ⟨$⟩ y)  ≈⟨ left-inverse y ⟩
    y                    ∎

  injection : Injection From To
  injection = record { to = to; injective = injective }

Surjective : ∀ {f₁ f₂ t₁ t₂} {F : Setoid f₁ f₂} {T : Setoid t₁ t₂} →
             F ⟶ T → Set _
Surjective f = ∃ λ g → f LeftInverseOf g

infixr 9 _∘_

id : ∀ {s₁ s₂} {S : Setoid s₁ s₂} → LeftInverse S S
id {S = S} = record
  { to           = F.id
  ; from         = F.id
  ; left-inverse = λ _ → Setoid.refl S
  }

_∘_ : ∀ {f₁ f₂ m₁ m₂ t₁ t₂}
        {F : Setoid f₁ f₂} {M : Setoid m₁ m₂} {T : Setoid t₁ t₂} →
      LeftInverse M T → LeftInverse F M → LeftInverse F T
_∘_ {F = F} f g = record
  { to           = to   f ⟪∘⟫ to   g
  ; from         = from g ⟪∘⟫ from f
  ; left-inverse = λ x → begin
      from g ⟨$⟩ (from f ⟨$⟩ (to f ⟨$⟩ (to g ⟨$⟩ x)))  ≈⟨ F.cong (from g) (left-inverse f (to g ⟨$⟩ x)) ⟩
      from g ⟨$⟩ (to g ⟨$⟩ x)                          ≈⟨ left-inverse g x ⟩
      x                                                ∎
  }
  where
  open LeftInverse
  open EqReasoning F
