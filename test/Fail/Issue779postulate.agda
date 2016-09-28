-- Andreas, 2016-07-28, issue #779

record P : Set where
  postulate Bla : Set
  field F : Set

-- Current error:
-- Missing definition for Bla

-- Expected:
-- Success, or error outlawing postulate before last field.
