-- Andreas, 2019-08-10

record R : Set₁ where
  indutive
  field A : Set

-- The error message is strange:

-- This declaration is illegal in a record before the last field
-- when scope checking the declaration
--   record R where
--     indutive
--     field A : Set

-- Andreas, 2026-11-11 By fixing #434, we now get this
-- error: [AbsentRHSRequiresAbsurdPattern]
-- The right-hand side can only be omitted if there is an absurd
-- pattern, () or {}, in the left-hand side.
-- when checking that the clause indutive has type _1
