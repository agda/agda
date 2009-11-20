------------------------------------------------------------------------
-- Operations on nullary relations (like negation and decidability)
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

-- Some operations on/properties of nullary relations, i.e. sets.

module Relation.Nullary where

open import Data.Product
open import Level
import Relation.Nullary.Core as Core
open import Relation.Binary
open import Relation.Binary.FunctionSetoid
import Relation.Binary.EqReasoning as EqReasoning

------------------------------------------------------------------------
-- Negation

open Core public using (¬_)

------------------------------------------------------------------------
-- Equivalence

infix 3 _⇔_

_⇔_ : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
P ⇔ Q = (P → Q) × (Q → P)

------------------------------------------------------------------------
-- Decidable relations

open Core public using (Dec; yes; no)

------------------------------------------------------------------------
-- Injections

Injective : ∀ {a₁ a₂ b₁ b₂} {A : Setoid a₁ a₂} {B : Setoid b₁ b₂} →
            A ⟶ B → Set _
Injective {A = A} {B} f = ∀ {x y} → f ⟨$⟩ x ≈₂ f ⟨$⟩ y → x ≈₁ y
  where
  open Setoid A renaming (_≈_ to _≈₁_)
  open Setoid B renaming (_≈_ to _≈₂_)

_LeftInverseOf_ : ∀ {a₁ a₂ b₁ b₂} {A : Setoid a₁ a₂} {B : Setoid b₁ b₂} →
                  B ⟶ A → A ⟶ B → Set _
_LeftInverseOf_ {A = A} f g = ∀ x → f ⟨$⟩ (g ⟨$⟩ x) ≈₁ x
  where open Setoid A renaming (_≈_ to _≈₁_)

record Injection {f₁ f₂ t₁ t₂}
                 (From : Setoid f₁ f₂) (To : Setoid t₁ t₂) :
                 Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  field
    to        : From ⟶ To
    injective : Injective to

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
    from ⟨$⟩ (to ⟨$⟩ x)  ≈⟨ pres from eq ⟩
    from ⟨$⟩ (to ⟨$⟩ y)  ≈⟨ left-inverse y ⟩
    y                    ∎

  injection : Injection From To
  injection = record { to = to; injective = injective }
