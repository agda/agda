------------------------------------------------------------------------
-- Inverses
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Function.Inverse where

open import Data.Product
open import Level
open import Relation.Binary
open import Function using (flip)
open import Function.Equality as F
  using (_⟶_) renaming (_∘_ to _⟪∘⟫_)
open import Function.LeftInverse as Left hiding (id; _∘_)
open import Function.Surjection  as Surj hiding (id; _∘_)
open import Function.Bijection   as Bi   hiding (id; _∘_)

-- Inverses.

record _InverseOf_ {f₁ f₂ t₁ t₂}
                   {From : Setoid f₁ f₂} {To : Setoid t₁ t₂}
                   (from : To ⟶ From) (to : From ⟶ To) :
                   Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  field
    left-inverse-of  : from LeftInverseOf  to
    right-inverse-of : from RightInverseOf to

-- The set of all inverses between two setoids.

record Inverse {f₁ f₂ t₁ t₂}
               (From : Setoid f₁ f₂) (To : Setoid t₁ t₂) :
               Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  field
    to         : From ⟶ To
    from       : To ⟶ From
    inverse-of : from InverseOf to

  open _InverseOf_ inverse-of public

  left-inverse : LeftInverse From To
  left-inverse = record
    { to              = to
    ; from            = from
    ; left-inverse-of = left-inverse-of
    }

  open LeftInverse left-inverse public
    using (injective; injection)

  bijection : Bijection From To
  bijection = record
    { to        = to
    ; bijective = record
      { injective  = injective
      ; surjective = record
        { from             = from
        ; right-inverse-of = right-inverse-of
        }
      }
    }

  open Bijection bijection public
    using (surjective; surjection; right-inverse)

------------------------------------------------------------------------
-- Inverse is an equivalence relation

-- Identity and composition (reflexivity and transitivity).

id : ∀ {s₁ s₂} → Reflexive (Inverse {s₁} {s₂})
id {x = S} = record
  { to         = F.id
  ; from       = F.id
  ; inverse-of = record
    { left-inverse-of  = LeftInverse.left-inverse-of id′
    ; right-inverse-of = LeftInverse.left-inverse-of id′
    }
  } where id′ = Left.id {S = S}

infixr 9 _∘_

_∘_ : ∀ {f₁ f₂ m₁ m₂ t₁ t₂} →
      TransFlip (Inverse {f₁} {f₂} {m₁} {m₂})
                (Inverse {m₁} {m₂} {t₁} {t₂})
                (Inverse {f₁} {f₂} {t₁} {t₂})
f ∘ g = record
  { to         = to   f ⟪∘⟫ to   g
  ; from       = from g ⟪∘⟫ from f
  ; inverse-of = record
    { left-inverse-of  = LeftInverse.left-inverse-of (Left._∘_ (left-inverse  f) (left-inverse  g))
    ; right-inverse-of = LeftInverse.left-inverse-of (Left._∘_ (right-inverse g) (right-inverse f))
    }
  } where open Inverse

-- Symmetry.

sym : ∀ {f₁ f₂ t₁ t₂} →
      Sym (Inverse {f₁} {f₂} {t₁} {t₂}) (Inverse {t₁} {t₂} {f₁} {f₂})
sym inv = record
  { from       = to
  ; to         = from
  ; inverse-of = record
    { left-inverse-of  = right-inverse-of
    ; right-inverse-of = left-inverse-of
    }
  } where open Inverse inv

-- Every unary relation induces an equivalence relation. (No claim is
-- made that this relation is unique.)

InducedEquivalence₁ : ∀ {a s₁ s₂} {A : Set a}
                      (S : A → Setoid s₁ s₂) → Setoid _ _
InducedEquivalence₁ S = record
  { _≈_           = λ x y → Inverse (S x) (S y)
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
  { _≈_           = λ x y → ∀ {z} → Inverse (z S x) (z S y)
  ; isEquivalence = record
    { refl  = id
    ; sym   = λ i≈j → sym i≈j
    ; trans = λ i≈j j≈k → j≈k ∘ i≈j
    }
  }
