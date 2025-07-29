-- Andreas, 2020-04-15, issue #4586.
-- Better error for invalid let pattern.
-- Andreas, 2025-07-06, issue #7989: irrelevant let now valid.

test : Set₁
test = let .Set = Set
       in  Set

-- WAS:
-- Set != x of type Set₁
-- when checking that the given dot pattern Set matches the inferred
-- value x

-- WAS: after fix of #4586:
-- Not a valid let pattern
-- when scope checking let .Set = Set in Set

-- Issue #7989: irrelevant let bindings are now legal.

-- EXPECTED: error: [VariableIsIrrelevant]
-- Variable Set is declared irrelevant, so it cannot be used here
-- when checking that the expression Set₁ has type Set₁

-- N.B. That Agda renames variable Set to Set₁ is very confusing in this error.
