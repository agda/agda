------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------

module Relation.Binary.PropositionalEquality where

open import Logic
open import Relation.Binary
open import Relation.Binary.Consequences
open import Relation.Binary.FunctionLifting
open import Data.Function
open import Data.Product

open import Relation.Binary.PropositionalEquality.Core public

------------------------------------------------------------------------
-- Some properties

≡-subst₁ :  {a : Set} -> (P : a -> Set1)
         -> forall {x y} -> x ≡ y -> P x -> P y
≡-subst₁ P ≡-refl p = p

≡-cong : Congruential _≡_
≡-cong = subst⟶cong ≡-reflexive ≡-subst

≡-cong₂ : Congruential₂ _≡_
≡-cong₂ = cong+trans⟶cong₂ ≡-cong ≡-trans

≡-setoid : Set -> Setoid
≡-setoid a = record
  { carrier       = a
  ; _≈_           = _≡_
  ; isEquivalence = ≡-isEquivalence
  }

≡-decSetoid : forall {a} -> Decidable (_≡_ {a}) -> DecSetoid
≡-decSetoid ≡-dec = record
  { carrier = _
  ; _≈_     = _≡_
  ; isDecEquivalence = record
      { isEquivalence = ≡-isEquivalence
      ; _≟_           = ≡-dec
      }
  }

≡-isPreorder : forall {a} -> IsPreorder {a} _≡_ _≡_
≡-isPreorder = record
  { isEquivalence = ≡-isEquivalence
  ; refl          = ≡-reflexive
  ; trans         = ≡-trans
  ; ≈-resp-∼      = ≡-resp _≡_
  }

≡-preorder : Set -> Preorder
≡-preorder a = record
  { carrier    = a
  ; _≈_        = _≡_
  ; _∼_        = _≡_
  ; isPreorder = ≡-isPreorder
  }

------------------------------------------------------------------------
-- Pointwise equality

infix 4 _≗_

_->-setoid_ : (a b : Set) -> Setoid
a ->-setoid b = LiftSetoid (≡-setoid a) (≡-setoid b) ≡-cong

_≗_ : {a b : Set} -> (f g : a -> b) -> Set
_≗_ {a} {b} = SetoidOps._≈_ (a ->-setoid b)

------------------------------------------------------------------------
-- The inspect idiom

data Inspect {a : Set} (x : a) : Set where
  _with-≡_ : (y : a) -> y ≡ x -> Inspect x

inspect : forall {a} (x : a) -> Inspect x
inspect x = x with-≡ ≡-refl

-- Example usage:

-- f x y with inspect (g x)
-- f x y | z with-≡ eq = ...

------------------------------------------------------------------------
-- Convenient syntax for equality reasoning

import Relation.Binary.EqReasoning as ER

-- Relation.Binary.EqReasoning is more convenient to use with _≡_ if
-- the combinators take the type argument (a) as a hidden argument,
-- instead of being locked to a fixed type at module instantiation
-- time.

module ≡-Reasoning where
  private
    module Dummy {a : Set} where
      open ER (≡-preorder a) public
        hiding (_≈⟨_⟩_; ≈-byDef)
        renaming (_∼⟨_⟩_ to _≡⟨_⟩_)
  open Dummy public
