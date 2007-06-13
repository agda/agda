------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------

module Prelude.BinaryRelation.PropositionalEquality where

open import Prelude.Logic
open import Prelude.BinaryRelation

abstract

  ≡-reflexive : {a : Set} -> Reflexive {a} _≡_ _≡_
  ≡-reflexive ≡-refl = ≡-refl

  ≡-sym : {a : Set} -> Symmetric {a} _≡_
  ≡-sym ≡-refl = ≡-refl

  ≡-trans : {a : Set} -> Transitive {a} _≡_
  ≡-trans ≡-refl ≡-refl = ≡-refl

  ≡-subst : {a : Set} -> Substitutive {a} _≡_
  ≡-subst P ≡-refl p = p

  ≡-cong : Congruential _≡_
  ≡-cong = subst⟶cong ≡-reflexive ≡-subst

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

≡-setoid : Set -> Setoid
≡-setoid a = record { carrier = a; _≈_ = _≡_; equiv = ≡-equivalence }
