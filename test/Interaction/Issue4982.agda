{-# OPTIONS --cubical #-}

open import Agda.Builtin.Nat

postulate
  _≡_   : {A : Set} → A → A → Set
  refl  : (A : Set) (x : A) → x ≡ x
  cong  : (A B : Set) (x y : A) (f : A → B) (x≡y : x ≡ y) → f x ≡ f y
  subst : (A : Set) (x y : A) (P : A → Set) → x ≡ y → P x → P y

apply : (A : Set) (B : A → Set) → ((x : A) → B x) → ((x : A) → B x)
apply _ _ f x = f x

postulate
  A : Set

record R (f : A → A) : Set where

postulate
  P : (f : A → A) → R f → Set

  _ :
    (f : A → A) (r : R f) →
    P f (subst (A → A) _ f R
           (cong _ _ _ _ (λ f → apply _ _ f 0) (refl _ (λ _ → {!!}))) r)
