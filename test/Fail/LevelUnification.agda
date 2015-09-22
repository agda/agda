
-- Level suc is not a constructor, and doesn't behave as one
-- for unification.
module LevelUnification where

open import Common.Level

data _≡_ {a}{A : Set a}(x : A) : ∀ {b}{B : Set b} → B → Set where
  refl : x ≡ x

sym : ∀ a b (A : Set (lsuc a)) (B : Set (lsuc b)) (x : A) (y : B) → x ≡ y → y ≡ x
sym a .a A .A x .x refl = refl

