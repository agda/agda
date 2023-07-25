{-# OPTIONS --large-indices #-}
-- Andreas, 2020-02-15
-- Test case by Jesper to prevent regressions when fixing #3541.

-- Jesper, 2019-09-12: The fix of #3541 introduced a regression: the
-- index of the equality type is treated as a positive argument.


postulate X : Set

module EqualityAsPredicate where

  data _≡_ (A : Set) : Set → Set where
    refl : A ≡ A

  data D : Set where
    c : D ≡ X → D

  data E : Set where
    c : X ≡ E → E

module EqualityAsRelation where

  data _≡_ : Set → Set → Set where
    refl : ∀{A} → A ≡ A

  data D : Set where
    c : D ≡ X → D

  data E : Set where
    c : X ≡ E → E

-- Expected:
-- Positivity checker rejects D and E in both variants.
