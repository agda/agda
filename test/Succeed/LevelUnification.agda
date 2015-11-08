{-# OPTIONS --universe-polymorphism #-}

-- Check that unification can handle levels
module LevelUnification where

open import Common.Level

data _≡_ {a}{A : Set a}(x : A) : ∀ {b}{B : Set b} → B → Set where
  refl : x ≡ x

sym₁ : ∀ a b (A : Set a)(B : Set b)(x : A)(y : B) → x ≡ y → y ≡ x
sym₁ a .a A .A x .x refl = refl

sym₂ : ∀ a b (A : Set (lsuc a))(B : Set b)(x : A)(y : B) → x ≡ y → y ≡ x
sym₂ a .(lsuc a) A .A x .x refl = refl

homogenous : ∀ a (A : Set a)(x y : A) → x ≡ y → Set₁
homogenous a A x .x refl = Set
