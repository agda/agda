------------------------------------------------------------------------
-- Propositional (intensional) equality
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Relation.Binary.PropositionalEquality where

open import Data.Function
open import Data.Product
open import Level
open import Relation.Binary
open import Relation.Binary.Consequences
open import Relation.Binary.FunctionSetoid

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

setoid : Set → Setoid
setoid a = record
  { carrier       = a
  ; _≈_           = _≡_
  ; isEquivalence = isEquivalence
  }

decSetoid : {A : Set} → Decidable (_≡_ {A = A}) → DecSetoid
decSetoid dec = record
  { _≈_              = _≡_
  ; isDecEquivalence = record
      { isEquivalence = isEquivalence
      ; _≟_           = dec
      }
  }

isPreorder : ∀ {a} → IsPreorder {a} _≡_ _≡_
isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = id
  ; trans         = trans
  ; ∼-resp-≈      = resp₂ _≡_
  }

preorder : Set → Preorder
preorder a = record
  { carrier    = a
  ; _≈_        = _≡_
  ; _∼_        = _≡_
  ; isPreorder = isPreorder
  }

------------------------------------------------------------------------
-- Pointwise equality

infix 4 _≗_

_→-setoid_ : (A B : Set) → Setoid
A →-setoid B = A ≡⇨ λ _ → setoid B

_≗_ : ∀ {a b} (f g : a → b) → Set
_≗_ {a} {b} = Setoid._≈_ (a →-setoid b)

→-to-⟶ : ∀ {A B} → (A → B) → setoid A ⟶ setoid B
→-to-⟶ f = record { _⟨$⟩_ = f; pres = cong f }

------------------------------------------------------------------------
-- The inspect idiom

-- The inspect idiom can be used when you want to pattern match on the
-- result r of some expression e, and you also need to "remember" that
-- r ≡ e.

data Inspect {a : Set} (x : a) : Set where
  _with-≡_ : (y : a) (eq : y ≡ x) → Inspect x

inspect : ∀ {a} (x : a) → Inspect x
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
    module Dummy {a : Set} where
      open EqR (setoid a) public
        hiding (_≡⟨_⟩_) renaming (_≈⟨_⟩_ to _≡⟨_⟩_)
  open Dummy public
