-- Andreas, 2024-07-19, PR #7379
-- The error `BothWithAndRHS` cannot be triggered, we get
-- `MissingWithClauses` instead.

f : Set₁
f with Set = Set

-- Current error:
-- Missing with clauses for function f
