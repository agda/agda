------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of homogeneous binary relations
------------------------------------------------------------------------

-- This file contains some core definitions which are reexported by
-- Relation.Binary or Relation.Binary.PropositionalEquality.

module Relation.Binary.Core where

open import Data.Product
open import Function
open import Level
open import Relation.Nullary

------------------------------------------------------------------------
-- Binary relations

-- Heterogeneous binary relations

REL : ∀ {a b} → Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ suc ℓ)
REL A B ℓ = A → B → Set ℓ

-- Homogeneous binary relations

Rel : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
Rel A ℓ = REL A A ℓ

------------------------------------------------------------------------
-- Simple properties of binary relations

infixr 4 _⇒_ _=[_]⇒_

-- Implication/containment. Could also be written ⊆.

_⇒_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
      REL A B ℓ₁ → REL A B ℓ₂ → Set _
P ⇒ Q = ∀ {i j} → P i j → Q i j

-- Generalised implication. If P ≡ Q it can be read as "f preserves
-- P".

_=[_]⇒_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
          Rel A ℓ₁ → (A → B) → Rel B ℓ₂ → Set _
P =[ f ]⇒ Q = P ⇒ (Q on f)

-- A synonym, along with a binary variant.

_Preserves_⟶_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
                (A → B) → Rel A ℓ₁ → Rel B ℓ₂ → Set _
f Preserves P ⟶ Q = P =[ f ]⇒ Q

_Preserves₂_⟶_⟶_ :
  ∀ {a b c ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : Set b} {C : Set c} →
  (A → B → C) → Rel A ℓ₁ → Rel B ℓ₂ → Rel C ℓ₃ → Set _
_+_ Preserves₂ P ⟶ Q ⟶ R =
  ∀ {x y u v} → P x y → Q u v → R (x + u) (y + v)

-- Reflexivity of _∼_ can be expressed as _≈_ ⇒ _∼_, for some
-- underlying equality _≈_. However, the following variant is often
-- easier to use.

Reflexive : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Reflexive _∼_ = ∀ {x} → x ∼ x

-- Irreflexivity is defined using an underlying equality.

Irreflexive : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
              REL A B ℓ₁ → REL A B ℓ₂ → Set _
Irreflexive _≈_ _<_ = ∀ {x y} → x ≈ y → ¬ (x < y)

-- Generalised symmetry.

Sym : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
      REL A B ℓ₁ → REL B A ℓ₂ → Set _
Sym P Q = P ⇒ flip Q

Symmetric : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Symmetric _∼_ = Sym _∼_ _∼_

-- Generalised transitivity.

Trans : ∀ {a b c ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : Set b} {C : Set c} →
        REL A B ℓ₁ → REL B C ℓ₂ → REL A C ℓ₃ → Set _
Trans P Q R = ∀ {i j k} → P i j → Q j k → R i k

-- A variant of Trans.

TransFlip : ∀ {a b c ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : Set b} {C : Set c} →
            REL A B ℓ₁ → REL B C ℓ₂ → REL A C ℓ₃ → Set _
TransFlip P Q R = ∀ {i j k} → Q j k → P i j → R i k

Transitive : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Transitive _∼_ = Trans _∼_ _∼_ _∼_

Antisymmetric : ∀ {a ℓ₁ ℓ₂} {A : Set a} → Rel A ℓ₁ → Rel A ℓ₂ → Set _
Antisymmetric _≈_ _≤_ = ∀ {x y} → x ≤ y → y ≤ x → x ≈ y

Asymmetric : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Asymmetric _<_ = ∀ {x y} → x < y → ¬ (y < x)

_Respects_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} → (A → Set ℓ₁) → Rel A ℓ₂ → Set _
P Respects _∼_ = ∀ {x y} → x ∼ y → P x → P y

_Respects₂_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} → Rel A ℓ₁ → Rel A ℓ₂ → Set _
P Respects₂ _∼_ =
  (∀ {x} → P x      Respects _∼_) ×
  (∀ {y} → flip P y Respects _∼_)

Substitutive : ∀ {a ℓ₁} {A : Set a} → Rel A ℓ₁ → (ℓ₂ : Level) → Set _
Substitutive {A = A} _∼_ p = (P : A → Set p) → P Respects _∼_

Decidable : ∀ {a b ℓ} {A : Set a} {B : Set b} → REL A B ℓ → Set _
Decidable _∼_ = ∀ x y → Dec (x ∼ y)

data Tri {a b c} (A : Set a) (B : Set b) (C : Set c) :
         Set (a ⊔ b ⊔ c) where
  tri< : ( a :   A) (¬b : ¬ B) (¬c : ¬ C) → Tri A B C
  tri≈ : (¬a : ¬ A) ( b :   B) (¬c : ¬ C) → Tri A B C
  tri> : (¬a : ¬ A) (¬b : ¬ B) ( c :   C) → Tri A B C

Trichotomous : ∀ {a ℓ₁ ℓ₂} {A : Set a} → Rel A ℓ₁ → Rel A ℓ₂ → Set _
Trichotomous _≈_ _<_ = ∀ x y → Tri (x < y) (x ≈ y) (x > y)
  where _>_ = flip _<_

record NonEmpty {a b ℓ} {A : Set a} {B : Set b}
                (T : REL A B ℓ) : Set (a ⊔ b ⊔ ℓ) where
  constructor nonEmpty
  field
    {x}   : A
    {y}   : B
    proof : T x y

------------------------------------------------------------------------
-- Propositional equality

-- This dummy module is used to avoid shadowing of the field named
-- refl defined in IsEquivalence below. The module is opened publicly
-- at the end of this file.

import Agda.Builtin.Equality as Dummy

infix 4 _≢_
_≢_ : ∀ {a} {A : Set a} → A → A → Set a
x ≢ y = ¬ x Dummy.≡ y

------------------------------------------------------------------------
-- Equivalence relations

-- The preorders of this library are defined in terms of an underlying
-- equivalence relation, and hence equivalence relations are not
-- defined in terms of preorders.

record IsEquivalence {a ℓ} {A : Set a}
                     (_≈_ : Rel A ℓ) : Set (a ⊔ ℓ) where
  field
    refl  : Reflexive _≈_
    sym   : Symmetric _≈_
    trans : Transitive _≈_

  reflexive : Dummy._≡_ ⇒ _≈_
  reflexive Dummy.refl = refl

open Dummy public
