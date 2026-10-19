-- Andreas, 2016-07-28, issue #779

data D : Set where c : D

record R : Set1 where
  bla : D → D
  bla c = c
  field F : Set

-- Current:
-- Not a valid let-definition

-- Expected:
-- Success, or error outlawing pattern matching definition before last field.

-- As of 2026-01-20:
-- error: [ShouldBeRecordPattern]
-- Expected record pattern
-- when checking that the pattern c has type D
