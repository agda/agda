-- Andreas, 2024-07-19, PR #7379
-- Trigger error SplitOnUnchecked

record R : Set

f : R → Set
f record{} = R

record R where

-- Expected error:
-- Cannot split on data type R whose definition has not yet been checked
-- when checking that the pattern record {} has type R
