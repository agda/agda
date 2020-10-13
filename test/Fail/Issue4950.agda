-- Andreas, 2020-09-28, issue #4950
-- Ranges for missing definitions should not include
-- non-missing definitions.

A B C : Set₁  -- only B should be highlighted

A = Set
C = Set

-- The following names are declared but not accompanied by a
-- definition: B

-- Error range was:
-- line,3-13

-- The error range should not include C nor Set₁.
-- line,3-4
