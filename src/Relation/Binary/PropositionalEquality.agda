------------------------------------------------------------------------
-- Propositional (intensional) equality
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Relation.Binary.PropositionalEquality where

open import Data.Function
open import Data.Function.Equality using (_≡⇨_; _⟶_)
open import Data.Product
open import Level
open import Relation.Binary
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
  ; ∼-resp-≈      = resp₂ _≡_
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
A →-setoid B = A ≡⇨ λ _ → setoid B

_≗_ : ∀ {a b} {A : Set a} {B : Set b} (f g : A → B) → Set _
_≗_ {A = A} {B} = Setoid._≈_ (A →-setoid B)

→-to-⟶ : ∀ {a b₁ b₂} {A : Set a} {B : Setoid b₁ b₂} →
         (A → Setoid.Carrier B) → setoid A ⟶ B
→-to-⟶ {B = B} f =
  record { _⟨$⟩_ = f; cong = Setoid.reflexive B ∘ cong f }

------------------------------------------------------------------------
-- The inspect idiom

-- The inspect idiom can be used when you want to pattern match on the
-- result r of some expression e, and you also need to "remember" that
-- r ≡ e.

data Inspect {a} {A : Set a} (x : A) : Set a where
  _with-≡_ : (y : A) (eq : y ≡ x) → Inspect x

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
