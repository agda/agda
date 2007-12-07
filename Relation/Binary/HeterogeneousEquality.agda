------------------------------------------------------------------------
-- Heterogeneous equality
------------------------------------------------------------------------

module Relation.Binary.HeterogeneousEquality where

open import Logic
open import Relation.Binary
open import Relation.Binary.Consequences
import Relation.Binary.PropositionalEquality as Homo
open import Data.Function
open import Data.Product

------------------------------------------------------------------------
-- Some properties

≅-reflexive-≡ : {a : Set} -> Reflexive {a} _≡_ (\x y -> x ≅ y)
≅-reflexive-≡ ≡-refl = ≅-refl

≅-reflexive :  {a : Set}
            -> Reflexive {a} (\x y -> x ≅ y) (\x y -> x ≅ y)
≅-reflexive ≅-refl = ≅-refl

≅-sym : forall {a b} {x : a} {y : b} -> x ≅ y -> y ≅ x
≅-sym ≅-refl = ≅-refl

≅-trans :  forall {a b c} {x : a} {y : b} {z : c}
        -> x ≅ y -> y ≅ z -> x ≅ z
≅-trans ≅-refl ≅-refl = ≅-refl

≅-subst : {a : Set} -> Substitutive {a} (\x y -> x ≅ y)
≅-subst P ≅-refl p = p

≅-subst₁ :  {a : Set} -> (P : a -> Set1)
         -> forall {x y} -> x ≅ y -> P x -> P y
≅-subst₁ P ≅-refl p = p

≅-subst-removable
  :  forall {a} (P : a -> Set) {x y} (eq : x ≅ y) z
  -> ≅-subst P eq z ≅ z
≅-subst-removable P ≅-refl z = ≅-refl

≡-subst-removable
  :  forall {a} (P : a -> Set) {x y} (eq : x ≡ y) z
  -> Homo.≡-subst P eq z ≅ z
≡-subst-removable P ≡-refl z = ≅-refl

≅-cong : Congruential (\x y -> x ≅ y)
≅-cong = subst⟶cong ≅-reflexive-≡ ≅-subst

≅-cong₂ : Congruential₂ (\x y -> x ≅ y)
≅-cong₂ = cong+trans⟶cong₂ ≅-cong ≅-trans

≅-resp : forall {a} (∼ : Rel a) -> (\x y -> x ≅ y) Respects₂ ∼
≅-resp _∼_ = subst⟶resp₂ _∼_ ≅-subst

≅-isEquivalence : forall {a} -> IsEquivalence {a} (\x y -> x ≅ y)
≅-isEquivalence = record
  { refl  = ≅-reflexive-≡
  ; sym   = ≅-sym
  ; trans = ≅-trans
  }

≅-setoid : Set -> Setoid
≅-setoid a = record
  { carrier       = a
  ; _≈_           = \x y -> x ≅ y
  ; isEquivalence = ≅-isEquivalence
  }

≅-decSetoid : forall {a} -> Decidable (\x y -> _≅_ {a} x y) -> DecSetoid
≅-decSetoid ≅-dec = record
  { carrier = _
  ; _≈_     = \x y -> x ≅ y
  ; isDecEquivalence = record
      { isEquivalence = ≅-isEquivalence
      ; _≟_           = ≅-dec
      }
  }

≅-isPreorder : forall {a} ->
               IsPreorder {a} (\x y -> x ≅ y) (\x y -> x ≅ y)
≅-isPreorder = record
  { isEquivalence = ≅-isEquivalence
  ; refl          = ≅-reflexive
  ; trans         = ≅-trans
  ; ≈-resp-∼      = ≅-resp (\x y -> x ≅ y)
  }

≅-isPreorder-≡ : forall {a} -> IsPreorder {a} _≡_ (\x y -> x ≅ y)
≅-isPreorder-≡ = record
  { isEquivalence = Homo.≡-isEquivalence
  ; refl          = ≅-reflexive-≡
  ; trans         = ≅-trans
  ; ≈-resp-∼      = Homo.≡-resp (\x y -> x ≅ y)
  }

≅-preorder : Set -> Preorder
≅-preorder a = record
  { carrier    = a
  ; _≈_        = _≡_
  ; _∼_        = \x y -> x ≅ y
  ; isPreorder = ≅-isPreorder-≡
  }

------------------------------------------------------------------------
-- The inspect idiom

data Inspect {a : Set} (x : a) : Set where
  _with-≅_ : (y : a) -> y ≅ x -> Inspect x

inspect : forall {a} (x : a) -> Inspect x
inspect x = x with-≅ ≅-refl

-- Example usage:

-- f x y with inspect (g x)
-- f x y | z with-≅ eq = ...

------------------------------------------------------------------------
-- Convenient syntax for equality reasoning

import Relation.Binary.EqReasoning as EqR

-- Relation.Binary.EqReasoning is more convenient to use with _≅_ if
-- the combinators take the type argument (a) as a hidden argument,
-- instead of being locked to a fixed type at module instantiation
-- time.

module ≅-Reasoning where
  private
    module Dummy {a : Set} where
      open EqR (≅-setoid a) public
        hiding (_≡⟨_⟩_; ≡-byDef)
        renaming (_≈⟨_⟩_ to _≅⟨_⟩_)
  open Dummy public
