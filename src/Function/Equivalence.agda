------------------------------------------------------------------------
-- Equivalence (coinhabitance)
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Function.Equivalence where

open import Function using (flip)
open import Function.Equality as F
  using (_⟶_; _⟨$⟩_) renaming (_∘_ to _⟪∘⟫_)
open import Level
open import Relation.Binary
import Relation.Binary.PropositionalEquality as P

-- Setoid equivalence.

record Equivalent {f₁ f₂ t₁ t₂}
                  (From : Setoid f₁ f₂) (To : Setoid t₁ t₂) :
                  Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  field
    to   : From ⟶ To
    from : To ⟶ From

-- Set equivalence.

infix 3 _⇔_

_⇔_ : ∀ {f t} → Set f → Set t → Set _
From ⇔ To = Equivalent (P.setoid From) (P.setoid To)

equivalent : ∀ {f t} {From : Set f} {To : Set t} →
             (From → To) → (To → From) → From ⇔ To
equivalent to from = record { to = P.→-to-⟶ to; from = P.→-to-⟶ from }

------------------------------------------------------------------------
-- Equivalent is an equivalence relation

-- Identity and composition (reflexivity and transitivity).

id : ∀ {s₁ s₂} → Reflexive (Equivalent {s₁} {s₂})
id {x = S} = record
  { to   = F.id
  ; from = F.id
  }

infixr 9 _∘_

_∘_ : ∀ {f₁ f₂ m₁ m₂ t₁ t₂} →
      TransFlip (Equivalent {f₁} {f₂} {m₁} {m₂})
                (Equivalent {m₁} {m₂} {t₁} {t₂})
                (Equivalent {f₁} {f₂} {t₁} {t₂})
f ∘ g = record
  { to   = to   f ⟪∘⟫ to   g
  ; from = from g ⟪∘⟫ from f
  } where open Equivalent

-- Symmetry.

sym : ∀ {f₁ f₂ t₁ t₂} →
      Sym (Equivalent {f₁} {f₂} {t₁} {t₂}) (Equivalent {t₁} {t₂} {f₁} {f₂})
sym eq = record
  { from       = to
  ; to         = from
  } where open Equivalent eq

-- Every unary relation induces an equivalence relation. (No claim is
-- made that this relation is unique.)

InducedEquivalence₁ : ∀ {a s₁ s₂} {A : Set a}
                      (S : A → Setoid s₁ s₂) → Setoid _ _
InducedEquivalence₁ S = record
  { _≈_           = λ x y → Equivalent (S x) (S y)
  ; isEquivalence = record
    { refl  = id
    ; sym   = sym
    ; trans = flip _∘_
    }
  }

-- Every binary relation induces an equivalence relation. (No claim is
-- made that this relation is unique.)

InducedEquivalence₂ : ∀ {a b s₁ s₂} {A : Set a} {B : Set b}
                      (_S_ : A → B → Setoid s₁ s₂) → Setoid _ _
InducedEquivalence₂ _S_ = record
  { _≈_           = λ x y → ∀ {z} → Equivalent (z S x) (z S y)
  ; isEquivalence = record
    { refl  = id
    ; sym   = λ i≈j → sym i≈j
    ; trans = λ i≈j j≈k → j≈k ∘ i≈j
    }
  }
