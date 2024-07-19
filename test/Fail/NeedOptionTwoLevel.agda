-- Andreas, 2024-07-19, PR #7379
-- Trigger error NeedOptionTwoLevel

{-# OPTIONS --no-two-level #-}

open import Agda.Primitive

postulate
  A : SSet

-- Expected error:
-- Universe SSet is disabled (use option --two-level to enable SSet)
