------------------------------------------------------------------------
-- Left inverses
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Function.LeftInverse where

open import Data.Product
open import Level
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary
open import Function.Equality as F
  using (_⟶_; _⟨$⟩_) renaming (_∘_ to _⟪∘⟫_)
open import Function.Equivalence using (Equivalent)
open import Function.Injection using (Injective; Injection)

-- Left and right inverses.

_LeftInverseOf_ :
  ∀ {f₁ f₂ t₁ t₂} {From : Setoid f₁ f₂} {To : Setoid t₁ t₂} →
  To ⟶ From → From ⟶ To → Set _
_LeftInverseOf_ {From = From} f g = ∀ x → f ⟨$⟩ (g ⟨$⟩ x) ≈ x
  where open Setoid From

_RightInverseOf_ :
  ∀ {f₁ f₂ t₁ t₂} {From : Setoid f₁ f₂} {To : Setoid t₁ t₂} →
  To ⟶ From → From ⟶ To → Set _
f RightInverseOf g = g LeftInverseOf f

-- The set of all left inverses between two setoids.

record LeftInverse {f₁ f₂ t₁ t₂}
                   (From : Setoid f₁ f₂) (To : Setoid t₁ t₂) :
                   Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  field
    to              : From ⟶ To
    from            : To ⟶ From
    left-inverse-of : from LeftInverseOf to

  open Setoid      From
  open EqReasoning From

  injective : Injective to
  injective {x} {y} eq = begin
    x                    ≈⟨ sym (left-inverse-of x) ⟩
    from ⟨$⟩ (to ⟨$⟩ x)  ≈⟨ F.cong from eq ⟩
    from ⟨$⟩ (to ⟨$⟩ y)  ≈⟨ left-inverse-of y ⟩
    y                    ∎

  injection : Injection From To
  injection = record { to = to; injective = injective }

  equivalent : Equivalent From To
  equivalent = record
    { to   = to
    ; from = from
    }

-- The set of all right inverses between two setoids.

RightInverse : ∀ {f₁ f₂ t₁ t₂}
               (From : Setoid f₁ f₂) (To : Setoid t₁ t₂) → Set _
RightInverse From To = LeftInverse To From

-- Identity and composition.

id : ∀ {s₁ s₂} {S : Setoid s₁ s₂} → LeftInverse S S
id {S = S} = record
  { to              = F.id
  ; from            = F.id
  ; left-inverse-of = λ _ → Setoid.refl S
  }

infixr 9 _∘_

_∘_ : ∀ {f₁ f₂ m₁ m₂ t₁ t₂}
        {F : Setoid f₁ f₂} {M : Setoid m₁ m₂} {T : Setoid t₁ t₂} →
      LeftInverse M T → LeftInverse F M → LeftInverse F T
_∘_ {F = F} f g = record
  { to              = to   f ⟪∘⟫ to   g
  ; from            = from g ⟪∘⟫ from f
  ; left-inverse-of = λ x → begin
      from g ⟨$⟩ (from f ⟨$⟩ (to f ⟨$⟩ (to g ⟨$⟩ x)))  ≈⟨ F.cong (from g) (left-inverse-of f (to g ⟨$⟩ x)) ⟩
      from g ⟨$⟩ (to g ⟨$⟩ x)                          ≈⟨ left-inverse-of g x ⟩
      x                                                ∎
  }
  where
  open LeftInverse
  open EqReasoning F
