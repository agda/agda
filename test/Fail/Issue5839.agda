-- Andreas, 2026-02-21, issue #5839, report and testcase by isovector

data Bug : Set where
  var_x : Bug

bug : Bug → Bug
bug x = {! !}

-- This fails the parser because `x` is a part of the constructor.
-- The error message should hint towards this.
-- In particular, it should mention `var_x` as possible culprit.

-- Expected error: [NoParseForLHS]
-- Could not parse the left-hand side bug x
-- Operators used in the grammar:
--   var_x (closed operator, unrelated) [var_x (...)]
-- when scope checking the left-hand side bug x in the definition of bug
