{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

data _≅_ {A : Set} (x : A) : {B : Set} → B → Set where
  refl : x ≅ x

test₁ : (A : Set) (x y : A) (z : Nat) → x ≡ y → x ≅ (suc z) → y ≅ 1 → Nat
test₁ A (suc z) (suc zero) .z refl refl refl = {!!}

test₂ : (A : Set) (x y : A) (z : Nat) → x ≡ y → x ≅ 1 → y ≅ (suc z) → Nat
test₂ A (suc zero) (suc z) .z refl refl refl = {!!}
