{-# OPTIONS --without-K #-}
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

test : {A : Set} {x₁ x₂ : A} {y : Nat} → c x₁ y ≡ c x₂ y → Set
test refl = Nat
