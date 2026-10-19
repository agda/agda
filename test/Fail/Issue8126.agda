-- Andreas, 2025-10-06, issue #8126
-- Do not print generalized variables as projections.

-- {-# OPTIONS -v tc.error.mismatchedProjections:40 #-}

open import Agda.Builtin.Equality

postulate
  A : Set
  P : A → Set
  c : A

variable
  a b : A

postulate
  foo : (x : P a) (y : P b) → x ≡ y

-- WAS error: [MismatchedProjectionsError]
-- The projections b and a do not match
-- when checking that the expression y has type P a

-- Expected error: [UnequalTerms]
-- b != a
-- when checking that the expression y has type P a
