-- Andreas, 2021-04-14, #1154
-- Andreas, 2021-04-10, BNFC/bnfc#354
-- Make sure we do not "resurrect" superseded layout columns.

private private private
  A : Set                -- OK, stacking
        B : Set          -- Bad, should fail

-- Expected: Parse error after B
