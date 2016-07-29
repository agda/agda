-- Andreas, 2016-07-28, issue #779

record R : Set1 where
  data Bla : Set where
  field F : Set

-- WAS:
-- Not a valid let-definition

-- Expected:
-- Success, or error outlawing pattern matching definition before last field.
