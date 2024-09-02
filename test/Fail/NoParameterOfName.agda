-- Andreas, 2024-07-19, PR #7379
-- Trigger error NoParameterOfName

data D {A : Set} : Set
data D {B = B} where

-- Expected error:
-- No parameter of name B
