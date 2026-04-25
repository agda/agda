-- Andreas, 2024-06-22, conflicting ETA pragma
-- Andreas, 2025-04-25, moved to its own test case

{-# ETA_EQUALITY #-}
record R : Set where
  coinductive; no-eta-equality

-- Expected error: [EtaPragmaVsNoEtaEquality]
-- Record has both ETA_EQUALITY pragma and no-eta-equality directive
-- when checking the definition of R
