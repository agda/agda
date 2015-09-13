-- Andreas, 2015-09-12, Issue 1637, reported by Nisse.
-- {-# OPTIONS -v tc.display:100 -v reify.display:100 #-}

record R (X : Set₁) : Set₁ where
  field
    f : X

postulate
  A : Set₁
  P : A → Set

module M (_ : Set₁) where

  Unrelated-function : R Set → Set
  Unrelated-function Y = R.f Y  -- eta expansion is necessary

open M Set

  -- Here, the old implementation recursively added a display form
  -- for R.f because the body of Unrelated-function has the right
  -- form, looking as if it came from a module application.

  -- adding display forms
  --   Issue1637.M.Unrelated-function --> Issue1637._.Unrelated-function
  --   Issue1637.R.f --> Issue1637._.Unrelated-function

  -- If one restricts display forms to things that actually
  -- come from a module applications, i.e., are a defCopy,
  -- then this issue is fixed.

Foo : ((Z : R A) → P (R.f Z)) → Set₁
Foo f = f

-- The inferred type of f is (printed as?)
--
--   (Z : R A) → P Unrelated-function,
--
-- which is not a type-correct expression.
--
-- The bug exists in Agda 2.3.2, but not in Agda 2.3.0.1.
