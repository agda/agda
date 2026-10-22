-- Andreas, 2024-07-19, PR #7379
-- Trigger error NoParameterOfName

data D {A : Set} : Set
data D {B = B} where

-- Andreas, 2026-10-22, issue #8739
-- Report also the names of available parameters.
--
-- Expected error: [NoParameterOfName]
-- No parameter of name B (possible parameters: A)
-- when checking the definition of D
