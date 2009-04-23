------------------------------------------------------------------------
-- Heterogeneous equality
------------------------------------------------------------------------

module Relation.Binary.HeterogeneousEquality where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Consequences
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)
open import Data.Function
open import Data.Product

------------------------------------------------------------------------
-- Heterogeneous equality

infix 4 _≅_ _≇_ _≅₁_ _≇₁_

data _≅_ {a : Set} (x : a) : {b : Set} → b → Set where
  refl : x ≅ x

data _≅₁_ {a : Set1} (x : a) : {b : Set1} → b → Set where
  refl : x ≅₁ x

-- Nonequality.

_≇_ : {a : Set} → a → {b : Set} → b → Set
x ≇ y = ¬ x ≅ y

_≇₁_ : {a : Set1} → a → {b : Set1} → b → Set
x ≇₁ y = ¬ x ≅₁ y

------------------------------------------------------------------------
-- Conversion

≡-to-≅ : ∀ {a} {x y : a} → x ≡ y → x ≅ y
≡-to-≅ refl = refl

≅-to-≡ : ∀ {a} {x y : a} → x ≅ y → x ≡ y
≅-to-≡ refl = refl

------------------------------------------------------------------------
-- Some properties

reflexive : ∀ {a} → _⇒_ {a} _≡_ (λ x y → x ≅ y)
reflexive refl = refl

sym : ∀ {a b} {x : a} {y : b} → x ≅ y → y ≅ x
sym refl = refl

trans : ∀ {a b c} {x : a} {y : b} {z : c} → x ≅ y → y ≅ z → x ≅ z
trans refl refl = refl

subst : ∀ {a} → Substitutive {a} (λ x y → x ≅ y)
subst P refl p = p

subst₁ : ∀ {a} (P : a → Set1) → ∀ {x y} → x ≅ y → P x → P y
subst₁ P refl p = p

subst-removable : ∀ {a} (P : a → Set) {x y} (eq : x ≅ y) z →
                  subst P eq z ≅ z
subst-removable P refl z = refl

≡-subst-removable : ∀ {a} (P : a → Set) {x y} (eq : x ≡ y) z →
                    PropEq.subst P eq z ≅ z
≡-subst-removable P refl z = refl

cong : Congruential (λ x y → x ≅ y)
cong = subst⟶cong refl subst

cong₂ : Congruential₂ (λ x y → x ≅ y)
cong₂ = cong+trans⟶cong₂ cong trans

resp : ∀ {a} (∼ : Rel a) → (λ x y → x ≅ y) Respects₂ ∼
resp _∼_ = subst⟶resp₂ _∼_ subst

isEquivalence : ∀ {a} → IsEquivalence {a} (λ x y → x ≅ y)
isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

setoid : Set → Setoid
setoid a = record
  { carrier       = a
  ; _≈_           = λ x y → x ≅ y
  ; isEquivalence = isEquivalence
  }

decSetoid : ∀ {a} → Decidable (λ x y → _≅_ {a} x y) → DecSetoid
decSetoid dec = record
  { _≈_              = λ x y → x ≅ y
  ; isDecEquivalence = record
      { isEquivalence = isEquivalence
      ; _≟_           = dec
      }
  }

isPreorder : ∀ {a} → IsPreorder {a} (λ x y → x ≅ y) (λ x y → x ≅ y)
isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = id
  ; trans         = trans
  ; ≈-resp-∼      = resp (λ x y → x ≅ y)
  }

isPreorder-≡ : ∀ {a} → IsPreorder {a} _≡_ (λ x y → x ≅ y)
isPreorder-≡ = record
  { isEquivalence = PropEq.isEquivalence
  ; reflexive     = reflexive
  ; trans         = trans
  ; ≈-resp-∼      = PropEq.resp (λ x y → x ≅ y)
  }

preorder : Set → Preorder
preorder a = record
  { carrier    = a
  ; _≈_        = _≡_
  ; _∼_        = λ x y → x ≅ y
  ; isPreorder = isPreorder-≡
  }

------------------------------------------------------------------------
-- The inspect idiom

-- See Relation.Binary.PropositionalEquality.Inspect.

data Inspect {a : Set} (x : a) : Set where
  _with-≅_ : (y : a) (eq : y ≅ x) → Inspect x

inspect : ∀ {a} (x : a) → Inspect x
inspect x = x with-≅ refl

------------------------------------------------------------------------
-- Convenient syntax for equational reasoning

import Relation.Binary.EqReasoning as EqR

-- Relation.Binary.EqReasoning is more convenient to use with _≅_ if
-- the combinators take the type argument (a) as a hidden argument,
-- instead of being locked to a fixed type at module instantiation
-- time.

module ≅-Reasoning where
  private
    module Dummy {a : Set} where
      open EqR (setoid a) public
        renaming (_≈⟨_⟩_ to _≅⟨_⟩_)
  open Dummy public
