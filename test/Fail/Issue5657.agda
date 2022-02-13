-- Andreas, 2021-11-19, issue #5657 reported by J Barrett
-- Regression in 2.6.2: internal error instead of error message

record R : Set₁ where
  field A : Set

postulate r : R
open R r

fail : Set
fail = r .A

-- WAS:
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: __IMPOSSIBLE__, called at src/full/Agda/TypeChecking/Rules/Application.hs:968

-- Expected:
-- Set should be a function type, but it isn't
-- when checking that r is a valid argument to a function of type Set
