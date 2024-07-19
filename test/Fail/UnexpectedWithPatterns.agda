-- Andreas, 2024-07-19, PR #7379
-- Trigger error UnexpectedWithPatterns

f : Set1
f | Set = Set

-- Expected error:
-- Unexpected with patterns | Set₁
-- when checking the definition of f
