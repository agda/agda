------------------------------------------------------------------------
-- Inverses
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Function.Inverse where

open import Level
open import Function as Fun using (flip)
open import Function.Bijection hiding (id; _∘_)
open import Function.Equality as F
  using (_⟶_) renaming (_∘_ to _⟪∘⟫_)
open import Function.Equivalence as Eq using (Equivalent; ⇔-setoid)
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
    using (equivalent; surjective; surjection; right-inverse)

-- The set of all inverses between two sets.

infix 3 _⇿_

_⇿_ : ∀ {f t} → Set f → Set t → Set _
From ⇿ To = Inverse (P.setoid From) (P.setoid To)

-- If two setoids are in bijective correspondence, then there is an
-- inverse between them.

fromBijection :
  ∀ {f₁ f₂ t₁ t₂} {From : Setoid f₁ f₂} {To : Setoid t₁ t₂} →
  Bijection From To → Inverse From To
fromBijection b = record
  { to         = Bijection.to b
  ; from       = Bijection.from b
  ; inverse-of = record
    { left-inverse-of  = Bijection.left-inverse-of b
    ; right-inverse-of = Bijection.right-inverse-of b
    }
  }

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

private
 module Dummy where

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

-- For fixed universe levels we can construct a setoid.

setoid : (s₁ s₂ : Level) → Setoid (suc (s₁ ⊔ s₂)) (s₁ ⊔ s₂)
setoid s₁ s₂ = record
  { Carrier       = Setoid s₁ s₂
  ; _≈_           = Inverse
  ; isEquivalence =
      record {refl = id; sym = Dummy.sym; trans = flip _∘_}
  }

------------------------------------------------------------------------
-- A generalisation which includes both _⇔_ and _⇿_

-- There are two kinds of "isomorphisms": equivalences and inverses.

data Kind : Set where
  equivalent inverse : Kind

Isomorphism : Kind → ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set _
Isomorphism inverse    A B = Inverse    (P.setoid A) (P.setoid B)
Isomorphism equivalent A B = Equivalent (P.setoid A) (P.setoid B)

-- Inverses are stronger, equivalences weaker.

⇿⇒ : ∀ {k x y} {X : Set x} {Y : Set y} →
     Isomorphism inverse X Y → Isomorphism k X Y
⇿⇒ {inverse}    = Fun.id
⇿⇒ {equivalent} = Inverse.equivalent

⇒⇔ : ∀ {k x y} {X : Set x} {Y : Set y} →
     Isomorphism k X Y → Isomorphism equivalent X Y
⇒⇔ {inverse}    = Inverse.equivalent
⇒⇔ {equivalent} = Fun.id

-- Equational reasoning for isomorphisms.

module EquationalReasoning where

  private

    refl : ∀ {k ℓ} → Reflexive (Isomorphism k {ℓ})
    refl {inverse}    = id
    refl {equivalent} = Eq.id

    trans : ∀ {k ℓ₁ ℓ₂ ℓ₃} →
            Trans (Isomorphism k {ℓ₁} {ℓ₂})
                  (Isomorphism k {ℓ₂} {ℓ₃})
                  (Isomorphism k {ℓ₁} {ℓ₃})
    trans {inverse}    = flip _∘_
    trans {equivalent} = flip Eq._∘_

  sym : ∀ {k ℓ₁ ℓ₂} →
        Sym (Isomorphism k {ℓ₁} {ℓ₂})
            (Isomorphism k {ℓ₂} {ℓ₁})
  sym {inverse}    = Dummy.sym
  sym {equivalent} = Eq.sym

  infix  2 _∎
  infixr 2 _≈⟨_⟩_ _⇿⟨_⟩_

  _≈⟨_⟩_ : ∀ {k x y z} (X : Set x) {Y : Set y} {Z : Set z} →
           Isomorphism k X Y → Isomorphism k Y Z → Isomorphism k X Z
  _ ≈⟨ X≈Y ⟩ Y≈Z = trans X≈Y Y≈Z

  _⇿⟨_⟩_ : ∀ {k x y z} (X : Set x) {Y : Set y} {Z : Set z} →
           X ⇿ Y → Isomorphism k Y Z → Isomorphism k X Z
  X ⇿⟨ X⇿Y ⟩ Y⇔Z = X ≈⟨ ⇿⇒ X⇿Y ⟩ Y⇔Z

  _∎ : ∀ {k x} (X : Set x) → Isomorphism k X X
  X ∎ = refl

-- For fixed universe levels we can construct a setoid.

Isomorphism-setoid : Kind → (ℓ : Level) → Setoid _ _
Isomorphism-setoid k ℓ = record
  { Carrier       = Set ℓ
  ; _≈_           = Isomorphism k
  ; isEquivalence =
      record {refl = _ ∎; sym = sym; trans = _≈⟨_⟩_ _}
  } where open EquationalReasoning

-- Every unary relation induces an equivalence relation. (No claim is
-- made that this relation is unique.)

InducedEquivalence₁ : Kind → ∀ {a s} {A : Set a}
                      (S : A → Set s) → Setoid _ _
InducedEquivalence₁ k S = record
  { _≈_           = λ x y → Isomorphism k (S x) (S y)
  ; isEquivalence = record {refl = refl; sym = sym; trans = trans}
  } where open Setoid (Isomorphism-setoid _ _)

-- Every binary relation induces an equivalence relation. (No claim is
-- made that this relation is unique.)

InducedEquivalence₂ : Kind → ∀ {a b s} {A : Set a} {B : Set b}
                      (_S_ : A → B → Set s) → Setoid _ _
InducedEquivalence₂ k _S_ = record
  { _≈_           = λ x y → ∀ {z} → Isomorphism k (z S x) (z S y)
  ; isEquivalence = record
    { refl  = refl
    ; sym   = λ i≈j → sym i≈j
    ; trans = λ i≈j j≈k → trans i≈j j≈k
    }
  } where open Setoid (Isomorphism-setoid _ _)

open Dummy public
