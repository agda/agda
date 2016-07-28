-- Andreas, 2016-07-28, issue #779

record R : Set1 where

  Bla : Set1
  Bla with Set
  ... | _ = Set

  field
    F : Set

-- Current error:
-- Missing definition for Bla

-- Expected:
-- Success, or error outlawing pattern matching definition before last field.
