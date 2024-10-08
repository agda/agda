-- Andreas, 2024-10-08, issue #2004 (and #7533)
-- Allow function symbols in DISPLAY pragma.

postulate
  A : Set
  f : A → A
  g : A → A
  P : A → Set

{-# DISPLAY f (g x) = x #-}

_ : (x : A) → P (f (g x))
_ = Set

-- Expected error:

-- Set₁ !=< (x : A) → P x
-- when checking that the expression Set has type (x : A) → P x
