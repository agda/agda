------------------------------------------------------------------------
-- Inverses
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Function.Inverse where

open import Level
open import Function using (flip)
open import Function.Bijection           hiding (id; _∘_)
open import Function.Equality as F
  using (_⟶_) renaming (_∘_ to _⟪∘⟫_)
open import Function.Equivalence using (Equivalent)
open import Function.LeftInverse as Left hiding (id; _∘_)
open import Function.Surjection  as Surj hiding (id; _∘_)
open import Relation.Binary
import Relation.Binary.PropositionalEquality as P

-- Inverses.

record _InverseOf_ {f₁ f₂ t₁ t₂}
                   {From : Setoid f₁ f₂} {To : Setoid t₁ t₂}
                   (from : To ⟶ From) (to : From ⟶ To) :
                   Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  field
    left-inverse-of  : from LeftInverseOf  to
    right-inverse-of : from RightInverseOf to

  equivalent : Equivalent From To
  equivalent = record
    { to   = to
    ; from = from
    }

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

-- The set of all inverses between two sets.

infix 3 _⇿_

_⇿_ : ∀ {f t} → Set f → Set t → Set _
From ⇿ To = Inverse (P.setoid From) (P.setoid To)

------------------------------------------------------------------------
-- Map and zip

map : ∀ {f₁ f₂ t₁ t₂} {From : Setoid f₁ f₂} {To : Setoid t₁ t₂}
        {f₁′ f₂′ t₁′ t₂′}
        {From′ : Setoid f₁′ f₂′} {To′ : Setoid t₁′ t₂′} →
      (t : (From ⟶ To) → (From′ ⟶ To′)) →
      (f : (To ⟶ From) → (To′ ⟶ From′)) →
      (∀ {to from} → from InverseOf to → f from InverseOf t to) →
      Inverse From To → Inverse From′ To′
map t f pres eq = record
  { to         = t to
  ; from       = f from
  ; inverse-of = pres inverse-of
  } where open Inverse eq

zip : ∀ {f₁₁ f₂₁ t₁₁ t₂₁}
        {From₁ : Setoid f₁₁ f₂₁} {To₁ : Setoid t₁₁ t₂₁}
        {f₁₂ f₂₂ t₁₂ t₂₂}
        {From₂ : Setoid f₁₂ f₂₂} {To₂ : Setoid t₁₂ t₂₂}
        {f₁ f₂ t₁ t₂} {From : Setoid f₁ f₂} {To : Setoid t₁ t₂} →
      (t : (From₁ ⟶ To₁) → (From₂ ⟶ To₂) → (From ⟶ To)) →
      (f : (To₁ ⟶ From₁) → (To₂ ⟶ From₂) → (To ⟶ From)) →
      (∀ {to₁ from₁ to₂ from₂} →
         from₁ InverseOf to₁ → from₂ InverseOf to₂ →
         f from₁ from₂ InverseOf t to₁ to₂) →
      Inverse From₁ To₁ → Inverse From₂ To₂ → Inverse From To
zip t f pres eq₁ eq₂ = record
  { to         = t (to   eq₁) (to   eq₂)
  ; from       = f (from eq₁) (from eq₂)
  ; inverse-of = pres (inverse-of eq₁) (inverse-of eq₂)
  } where open Inverse

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
