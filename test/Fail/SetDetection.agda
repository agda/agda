{-# OPTIONS --cubical-compatible #-}
open import Common.Prelude
open import Common.Equality

KNat : {x : Nat} (e : x ≡ x) → e ≡ refl
KNat refl = refl

KEqNat : {x : Nat} {e : x ≡ x} (p : e ≡ e) → p ≡ refl
KEqNat refl = refl

KListNat : {x : List Nat} (e : x ≡ x) → e ≡ refl
KListNat refl = refl

data D (A : Set) : Nat → Set where
  c : (x : A)(y : Nat) → D A y

-- Jesper 2015-12-18: this test case doesn't work yet with the new unifier
-- We need generalization of indices when applying the injectivity rule
--test : {A : Set} {x₁ x₂ : A} {y : Nat} → c x₁ y ≡ c x₂ y → Set
--test refl = Nat
