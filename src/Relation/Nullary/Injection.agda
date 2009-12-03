------------------------------------------------------------------------
-- Injections
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Relation.Nullary.Injection where

open import Data.Function as Fun using () renaming (_∘_ to _⟨∘⟩_)
open import Level
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary
open import Relation.Binary.FunctionSetoid as F
  using (_⟶_; _⟨$⟩_) renaming (_∘_ to _⟪∘⟫_)

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

infixr 9 _∘_

id : ∀ {s₁ s₂} {S : Setoid s₁ s₂} → Injection S S
id = record { to = F.id; injective = Fun.id }

_∘_ : ∀ {f₁ f₂ m₁ m₂ t₁ t₂}
        {F : Setoid f₁ f₂} {M : Setoid m₁ m₂} {T : Setoid t₁ t₂} →
      Injection M T → Injection F M → Injection F T
f ∘ g = record
  { to        =          to        f  ⟪∘⟫ to        g
  ; injective = (λ {_} → injective g) ⟨∘⟩ injective f
  }  where open Injection
