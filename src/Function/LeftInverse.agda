------------------------------------------------------------------------
-- The Agda standard library
--
-- Left inverses
------------------------------------------------------------------------

module Function.LeftInverse where

open import Data.Product
open import Level
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary
open import Function.Equality as Eq
  using (_⟶_; _⟨$⟩_) renaming (_∘_ to _⟪∘⟫_)
open import Function.Equivalence using (Equivalence)
open import Function.Injection using (Injective; Injection)
import Relation.Binary.PropositionalEquality as P

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

  private
    open module F = Setoid From
    open module T = Setoid To
  open EqReasoning From

  injective : Injective to
  injective {x} {y} eq = begin
    x                    ≈⟨ F.sym (left-inverse-of x) ⟩
    from ⟨$⟩ (to ⟨$⟩ x)  ≈⟨ Eq.cong from eq ⟩
    from ⟨$⟩ (to ⟨$⟩ y)  ≈⟨ left-inverse-of y ⟩
    y                    ∎

  injection : Injection From To
  injection = record { to = to; injective = injective }

  equivalence : Equivalence From To
  equivalence = record
    { to   = to
    ; from = from
    }

  to-from : ∀ {x y} → to ⟨$⟩ x T.≈ y → from ⟨$⟩ y F.≈ x
  to-from {x} {y} to-x≈y = begin
    from ⟨$⟩ y           ≈⟨ Eq.cong from (T.sym to-x≈y) ⟩
    from ⟨$⟩ (to ⟨$⟩ x)  ≈⟨ left-inverse-of x ⟩
    x                    ∎

-- The set of all right inverses between two setoids.

RightInverse : ∀ {f₁ f₂ t₁ t₂}
               (From : Setoid f₁ f₂) (To : Setoid t₁ t₂) → Set _
RightInverse From To = LeftInverse To From

-- The set of all left inverses from one set to another. (Read A ↞ B
-- as "surjection from B to A".)

infix 3 _↞_

_↞_ : ∀ {f t} → Set f → Set t → Set _
From ↞ To = LeftInverse (P.setoid From) (P.setoid To)

-- Identity and composition.

id : ∀ {s₁ s₂} {S : Setoid s₁ s₂} → LeftInverse S S
id {S = S} = record
  { to              = Eq.id
  ; from            = Eq.id
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
      from g ⟨$⟩ (from f ⟨$⟩ (to f ⟨$⟩ (to g ⟨$⟩ x)))  ≈⟨ Eq.cong (from g) (left-inverse-of f (to g ⟨$⟩ x)) ⟩
      from g ⟨$⟩ (to g ⟨$⟩ x)                          ≈⟨ left-inverse-of g x ⟩
      x                                                ∎
  }
  where
  open LeftInverse
  open EqReasoning F
