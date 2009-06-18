------------------------------------------------------------------------
-- Propositional (intensional) equality
------------------------------------------------------------------------

module Relation.Binary.PropositionalEquality where

open import Relation.Binary
open import Relation.Binary.Consequences
open import Relation.Binary.FunctionSetoid
open import Data.Function
open import Data.Product

-- Some of the definitions can be found in the following modules:

open import Relation.Binary.Core public using (_≡_; refl; _≢_)
open import Relation.Binary.PropositionalEquality.Core public

------------------------------------------------------------------------
-- Some properties

subst₂ : ∀ {A B} (P : A → B → Set) →
         ∀ {x₁ x₂ y₁ y₂} → x₁ ≡ x₂ → y₁ ≡ y₂ → P x₁ y₁ → P x₂ y₂
subst₂ P refl refl p = p

subst₁ : ∀ {a} (P : a → Set₁) → ∀ {x y} → x ≡ y → P x → P y
subst₁ P refl p = p

cong : Congruential _≡_
cong = subst⟶cong refl subst

cong₂ : Congruential₂ _≡_
cong₂ = cong+trans⟶cong₂ cong trans

setoid : Set → Setoid
setoid a = record
  { carrier       = a
  ; _≈_           = _≡_
  ; isEquivalence = isEquivalence
  }

decSetoid : ∀ {a} → Decidable (_≡_ {a}) → DecSetoid
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
