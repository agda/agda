-- Andreas, 2020-09-09, issue #4880
-- Make sure that duplicate hiding info is an error.

module _ (A B : Set) where

postulate
  _ : { { A } } → B

  _ : { { A } } → B

-- Expected: 2 fatal warnings
-- For instance:
-- {A} cannot appear by itself. It needs to be the argument to a
-- function expecting an implicit argument.
-- when scope checking {A}
