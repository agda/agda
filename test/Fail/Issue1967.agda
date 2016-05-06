-- Andreas, 2016-05-06, issue 1967

postulate
  D : {{A : Set}} → Set
  test : (A : Set) → D A

-- Expected error:
-- Set should be a function type, but it isn't
-- when checking that A is a valid argument to a function of type
-- {{A = A₁ : Set}} → Set
