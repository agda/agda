-- Andreas, AIM XXXV, 2022-05-09, issue #5728
-- Give a proper error rather than crashing.

test : Set
test with Set
...

-- This used to be an internal error.
-- Expected error now:
-- The right-hand side can only be omitted if there is an absurd
-- pattern, () or {}, in the left-hand side.
