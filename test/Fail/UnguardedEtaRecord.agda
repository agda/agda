-- Andreas, 2026-04-23, PR #8533
-- Trigger error UnguardedEtaRecord

{-# OPTIONS --eta-equality #-}  -- Redundant, but make sure default is eta.

record R : Set where
  inductive
  field f : R

-- Expected error: [UnguardedEtaRecord]
-- Recursive occurrence of this record in its definition is unguarded,
-- so eta-equality for this record might lead to non-termination in
-- the type checker.
-- To suppress this error, use pragma {-# ETA_EQUALITY #-}
