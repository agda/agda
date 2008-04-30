------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------

module Relation.Binary.PropositionalEquality1 where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; ≡-refl)

------------------------------------------------------------------------
-- Propositional equality

infix 4 _≡₁_ _≢₁_

data _≡₁_ {a : Set1} (x : a) : a -> Set where
  ≡₁-refl : x ≡₁ x

-- Nonequality.

_≢₁_ : {a : Set1} -> a -> a -> Set
x ≢₁ y = ¬ x ≡₁ y

------------------------------------------------------------------------
-- Some properties

≡₁-reflexive : {a : Set1} -> (x : a) -> x ≡₁ x
≡₁-reflexive _ = ≡₁-refl

≡₁-sym : {a : Set1} {x y : a} -> x ≡₁ y -> y ≡₁ x
≡₁-sym ≡₁-refl = ≡₁-refl

≡₁-trans :  {a : Set1} {x y z : a}
         -> x ≡₁ y -> y ≡₁ z -> x ≡₁ z
≡₁-trans ≡₁-refl ≡₁-refl = ≡₁-refl

≡₁-subst : {a b : Set} -> a ≡₁ b -> a -> b
≡₁-subst ≡₁-refl x = x

≡₁-cong :  forall {a b} -> (f : a -> b)
        -> forall {x y} -> x ≡₁ y -> f x ≡₁ f y
≡₁-cong _ ≡₁-refl = ≡₁-refl

≡₀₁-cong :  forall {a b} -> (f : a -> b)
         -> forall {x y} -> x ≡ y -> f x ≡₁ f y
≡₀₁-cong _ ≡-refl = ≡₁-refl
