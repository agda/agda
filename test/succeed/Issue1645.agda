-- Andreas, 2015-09-12

open import Common.Product
open import Common.Equality

module _ (A : Set) where

mutual
  X : A × A → A
  X = _

  test : (x y : A × A) → X (proj₁ x , proj₁ y) ≡ proj₁ x
  test _ _ = refl

-- This worked even before the fix of #1316,
-- since _ record variables are expanded (see #473).
