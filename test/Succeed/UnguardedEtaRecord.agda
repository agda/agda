-- Andreas, 2026-04-23, PR #8533
-- Trigger warning UnguardedEtaRecord

record R : Set where
  inductive; eta-equality
  field f : R

-- Expected warning: warning: -W[no]UnguardedEtaRecord
-- Recursive occurrence of this record in its definition is unguarded,
-- so eta-equality for this record might lead to non-termination in
-- the type checker.
-- To disable this warning, use pragma {-# ETA_EQUALITY #-}
