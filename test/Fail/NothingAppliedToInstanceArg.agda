-- Andreas, 2024-07-19, PR #7379
-- Trigger error NothingAppliedToInstanceArg

bad = {{x}}

-- Expected error:
-- ⦃ x ⦄ cannot appear by itself.
-- It needs to be the argument to a function expecting an instance argument.
-- when scope checking ⦃ x ⦄
