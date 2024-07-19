-- Andreas, 2024-07-19, PR #7379
-- Trigger error NotImplemented

postulate
  A B : Set
  x : A | B

-- Expected error:
-- Not implemented: type checking of with application
-- when checking that the expression A | B has type _0
