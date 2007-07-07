------------------------------------------------------------------------
-- Heterogeneous equality
------------------------------------------------------------------------

module Relation.Binary.HeterogeneousEquality where

open import Logic
open import Relation.Binary
import Relation.Binary.PropositionalEquality as Homo

------------------------------------------------------------------------
-- Some properties

≅-reflexive-≡ : {a : Set} -> Reflexive {a} _≡_ (\x y -> x ≅ y)
≅-reflexive-≡ ≡-refl = ≅-refl

≅-reflexive :  {a : Set}
            -> Reflexive {a} (\x y -> x ≅ y) (\x y -> x ≅ y)
≅-reflexive ≅-refl = ≅-refl

≅-sym : {a : Set} -> Symmetric {a} (\x y -> x ≅ y)
≅-sym ≅-refl = ≅-refl

≅-trans : {a : Set} -> Transitive {a} (\x y -> x ≅ y)
≅-trans ≅-refl ≅-refl = ≅-refl

≅-subst : {a : Set} -> Substitutive {a} (\x y -> x ≅ y)
≅-subst P ≅-refl p = p

≅-subst₁ :  {a : Set} -> (P : a -> Set1)
         -> forall {x y} -> x ≅ y -> P x -> P y
≅-subst₁ P ≅-refl p = p

≅-cong : Congruential (\x y -> x ≅ y)
≅-cong = subst⟶cong ≅-reflexive-≡ ≅-subst

≅-cong₂ : Congruential₂ (\x y -> x ≅ y)
≅-cong₂ = cong+trans⟶cong₂ ≅-cong ≅-trans

≅-preorder : forall {a} -> Preorder {a} (\x y -> x ≅ y) (\x y -> x ≅ y)
≅-preorder = record
  { refl  = ≅-reflexive
  ; trans = ≅-trans
  }

≅-preorder-≡ : forall {a} -> Preorder {a} _≡_ (\x y -> x ≅ y)
≅-preorder-≡ = record
  { refl  = ≅-reflexive-≡
  ; trans = ≅-trans
  }

≅-equivalence : forall {a} -> Equivalence {a} (\x y -> x ≅ y)
≅-equivalence {a} = record
  { preorder = ≅-preorder-≡
  ; sym      = ≅-sym
  }

≅-preSetoid : Set -> PreSetoid
≅-preSetoid a = record
  { carrier  = a
  ; _∼_      = \x y -> x ≅ y
  ; _≈_      = _≡_
  ; preorder = ≅-preorder-≡
  ; equiv    = Homo.≡-equivalence
  }

≅-setoid : Set -> Setoid
≅-setoid a = record
  { carrier = a
  ; _≈_     = \x y -> x ≅ y
  ; equiv   = ≅-equivalence
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

import Relation.Binary.EqReasoning as ER

-- Relation.Binary.EqReasoning is more convenient to use with _≅_ if
-- the combinators take the type argument (a) as a hidden argument,
-- instead of being locked to a fixed type at module instantiation
-- time.

module ≅-Reasoning where
  module ER-≅ {a : Set} where
    private
      module ER' = ER (≅-preSetoid a)
        hiding (_≈⟨_⟩_; ≈-byDef)
        renaming (_∼⟨_⟩_ to _≅⟨_⟩_)
    open ER' public
  open ER-≅ public
