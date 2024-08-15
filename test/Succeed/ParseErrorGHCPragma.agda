{-# OPTIONS --no-main #-}

-- Andreas, 2024-08-12
-- Trigger warning "Failed to parse GHC pragma"

postulate
  A : Set

{-# COMPILE GHC A #-}

-- Expected warning upon compilation:
--
-- Failed to parse GHC pragma ''
