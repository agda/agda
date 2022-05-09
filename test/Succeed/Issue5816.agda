-- AIM XXXV, 2022-05-09, issue #5816.
-- Regression on Agda master (2.6.3):
-- --without-K creates extra data constructors and function clauses
-- but crashes with --prop.

{-# OPTIONS --without-K #-}
{-# OPTIONS --prop #-}

open import Agda.Builtin.Nat

data _≤_ : Nat → Nat → Prop where
  z≤x : ∀ {x} → zero ≤ x
  s≤s : ∀ {x y} → x ≤ y → suc x ≤ suc y

x≤Sy : ∀ {x y} → x ≤ y → x ≤ suc y
x≤Sy z≤x     = z≤x
x≤Sy (s≤s p) = s≤s (x≤Sy p)

-- Crashed when generating extra transports from matches on a Prop.
-- Should succeed.

open import Agda.Builtin.Equality

data _≐_ {ℓ} {A : Set ℓ} (x : A) : A → Prop ℓ where
  refl' : x ≐ x

squash-≡ : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → x ≐ y
squash-≡ refl = refl'

-- Crashed when generating extra clauses.
-- Now skips generating extra clauses when targeting a Prop.
