-- Andreas, 2026-08-27, issue #8688.
-- The occurrence analysis now also descends into sorts,
-- so the occurrence of D in the level of the universe Set (g D)
-- is now seen by the positivity checker.

open import Agda.Primitive

postulate
  g : Setω → Level

data D : Setω where
  c : Set (g D) → D

-- Expected error: [NotStrictlyPositive]
-- D is not strictly positive, because it occurs
-- in the first argument of g
-- in a sort
-- in the type of the constructor c
-- in the definition of D.
