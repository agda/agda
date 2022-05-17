-- Andreas, 2021-10-08, first test case for unsupported generalization

variable
  X : Set

Y = X

-- Expected:
-- Generalizable variable GeneralizeRHS.X is not supported here
-- when scope checking X
