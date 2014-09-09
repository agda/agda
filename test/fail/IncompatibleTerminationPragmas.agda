-- Andreas, 2014-09-09

mutual
  {-# NON_TERMINATING #-}
  f : Set
  f = g

  {-# NO_TERMINATION_CHECK #-}
  g : Set
  g = f

-- Expected error:
-- In a mutual block, either all functions must have the same (or no)
-- termination checking pragma.
