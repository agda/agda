-- Andreas, 2019-08-10

record R : Set₁ where
  indutive
  field A : Set

-- The error message is strange:

-- This declaration is illegal in a record before the last field
-- when scope checking the declaration
--   record R where
--     indutive
--     field A : Set
