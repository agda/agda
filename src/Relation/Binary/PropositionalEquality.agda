------------------------------------------------------------------------
-- Propositional (intensional) equality
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Relation.Binary.PropositionalEquality where

open import Function
open import Function.Equality using (Π; _⟶_; ≡-setoid)
open import Data.Product
open import Level
open import Relation.Binary
import Relation.Binary.Indexed as I
open import Relation.Binary.Consequences

-- Some of the definitions can be found in the following modules:

open import Relation.Binary.Core public using (_≡_; refl; _≢_)
open import Relation.Binary.PropositionalEquality.Core public

------------------------------------------------------------------------
-- Some properties

subst₂ : ∀ {a b p} {A : Set a} {B : Set b} (P : A → B → Set p)
         {x₁ x₂ y₁ y₂} → x₁ ≡ x₂ → y₁ ≡ y₂ → P x₁ y₁ → P x₂ y₂
subst₂ P refl refl p = p

cong : ∀ {a b} {A : Set a} {B : Set b}
       (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
        (f : A → B → C) {x y u v} → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

proof-irrelevance : ∀ {a} {A : Set a} {x y : A} (p q : x ≡ y) → p ≡ q
proof-irrelevance refl refl = refl

setoid : ∀ {a} → Set a → Setoid _ _
setoid A = record
  { Carrier       = A
  ; _≈_           = _≡_
  ; isEquivalence = isEquivalence
  }

decSetoid : ∀ {a} {A : Set a} → Decidable (_≡_ {A = A}) → DecSetoid _ _
decSetoid dec = record
  { _≈_              = _≡_
  ; isDecEquivalence = record
      { isEquivalence = isEquivalence
      ; _≟_           = dec
      }
  }

isPreorder : ∀ {a} {A : Set a} → IsPreorder {A = A} _≡_ _≡_
isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = id
  ; trans         = trans
  }

preorder : ∀ {a} → Set a → Preorder _ _ _
preorder A = record
  { Carrier    = A
  ; _≈_        = _≡_
  ; _∼_        = _≡_
  ; isPreorder = isPreorder
  }

------------------------------------------------------------------------
-- Pointwise equality

infix 4 _≗_

_→-setoid_ : ∀ {a b} (A : Set a) (B : Set b) → Setoid _ _
A →-setoid B = ≡-setoid A (Setoid.indexedSetoid (setoid B))

_≗_ : ∀ {a b} {A : Set a} {B : Set b} (f g : A → B) → Set _
_≗_ {A = A} {B} = Setoid._≈_ (A →-setoid B)

:→-to-Π : ∀ {a b₁ b₂} {A : Set a} {B : I.Setoid _ b₁ b₂} →
          ((x : A) → I.Setoid.Carrier B x) → Π (setoid A) B
:→-to-Π {B = B} f = record { _⟨$⟩_ = f; cong = cong′ }
  where
  open I.Setoid B using (_≈_)

  cong′ : ∀ {x y} → x ≡ y → f x ≈ f y
  cong′ refl = I.Setoid.refl B

→-to-⟶ : ∀ {a b₁ b₂} {A : Set a} {B : Setoid b₁ b₂} →
         (A → Setoid.Carrier B) → setoid A ⟶ B
→-to-⟶ = :→-to-Π

------------------------------------------------------------------------
-- The inspect idiom

-- The inspect idiom can be used when you want to pattern match on the
-- result r of some expression e, and you also need to "remember" that
-- r ≡ e.

data Inspect {a} {A : Set a} (x : A) : Set a where
  _with-≡_ : (y : A) (eq : x ≡ y) → Inspect x

inspect : ∀ {a} {A : Set a} (x : A) → Inspect x
inspect x = x with-≡ refl

-- Example usage:

-- f x y with inspect (g x)
-- f x y | c z with-≡ eq = ...

------------------------------------------------------------------------
-- Convenient syntax for equational reasoning

import Relation.Binary.EqReasoning as EqR

-- Relation.Binary.EqReasoning is more convenient to use with _≡_ if
-- the combinators take the type argument (a) as a hidden argument,
-- instead of being locked to a fixed type at module instantiation
-- time.

module ≡-Reasoning where
  private
    module Dummy {a} {A : Set a} where
      open EqR (setoid A) public
        hiding (_≡⟨_⟩_) renaming (_≈⟨_⟩_ to _≡⟨_⟩_)
  open Dummy public

------------------------------------------------------------------------
-- Definition of functional extensionality

-- If _≡_ were extensional, then the following statement could be
-- proved.

Extensionality : (a b : Level) → Set _
Extensionality a b =
  {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
  (∀ x → f x ≡ g x) → f ≡ g
