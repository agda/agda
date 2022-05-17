-- Andreas, 2021-04-14, #1154
-- Andreas, 2021-04-12, BNFC/bnfc#354
-- Make sure we confirm tentative layout columns on first newline.

private private private A : Set
                        B : Set  -- all three blocks (8,16,24) should be confirmed here
                private          -- the column for this block needs to be > 16
  Bad : Set                      -- bad indentation, needs to be 0,8,16 or greater

-- Expected: Parse error after Bad
