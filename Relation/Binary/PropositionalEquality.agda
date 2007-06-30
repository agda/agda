------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------

module Relation.Binary.PropositionalEquality where

open import Logic
open import Relation.Binary
open import Relation.Binary.FunctionLifting

------------------------------------------------------------------------
-- Some properties

≡-reflexive : {a : Set} -> Reflexive {a} _≡_ _≡_
≡-reflexive ≡-refl = ≡-refl

≡-sym : {a : Set} -> Symmetric {a} _≡_
≡-sym ≡-refl = ≡-refl

≡-trans : {a : Set} -> Transitive {a} _≡_
≡-trans ≡-refl ≡-refl = ≡-refl

≡-subst : {a : Set} -> Substitutive {a} _≡_
≡-subst P ≡-refl p = p

≡-subst₁ :  {a : Set} -> (P : a -> Set1)
         -> forall {x y} -> x ≡ y -> P x -> P y
≡-subst₁ P ≡-refl p = p

≡-cong : Congruential _≡_
≡-cong = subst⟶cong ≡-reflexive ≡-subst

≡-cong₂ : Congruential₂ _≡_
≡-cong₂ = cong+trans⟶cong₂ ≡-cong ≡-trans

≡-preorder : forall {a} -> Preorder {a} _≡_ _≡_
≡-preorder = record
  { refl  = ≡-reflexive
  ; trans = ≡-trans
  }

≡-equivalence : forall {a} -> Equivalence {a} _≡_
≡-equivalence {a} = record
  { preorder = ≡-preorder
  ; sym      = ≡-sym
  }

≡-preSetoid : Set -> PreSetoid
≡-preSetoid a = record
  { carrier  = a
  ; _∼_      = _≡_
  ; preorder = ≡-preorder
  }

≡-setoid : Set -> Setoid
≡-setoid a = record
  { carrier = a
  ; _≈_     = _≡_
  ; equiv   = ≡-equivalence
  }

------------------------------------------------------------------------
-- Pointwise equality

_->-setoid_ : (a b : Set) -> Setoid
a ->-setoid b = LiftSetoid (≡-setoid a) (≡-setoid b) ≡-cong

_≗_ : {a b : Set} -> (f g : a -> b) -> Set
_≗_ {a} {b} = Setoid._≈_ (a ->-setoid b)

------------------------------------------------------------------------
-- The inspect idiom

data Inspect {a : Set} (x : a) : Set where
  _with-≡_ : (y : a) -> y ≡ x -> Inspect x

inspect : forall {a} (x : a) -> Inspect x
inspect x = x with-≡ ≡-refl

-- Example usage:

-- f x y with inspect (g x)
-- f x y | z with-≡ eq = ...
