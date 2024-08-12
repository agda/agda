-- Andreas, 2024-08-12
-- Reproduce error "Failed to parse GHC pragma"

postulate
  A : Set

{-# COMPILE GHC A #-}

-- Expected error:
--
-- Failed to parse GHC pragma ''
