------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------

module Relation.Binary.PropositionalEquality1 where

open import Logic
open import Relation.Binary

abstract

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
