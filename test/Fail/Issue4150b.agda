-- Andreas, 2026-02-28, issue #4150
-- Prefer MissingTypeSignature error over NotInScope error.

mutual
  data D where
    c : (A : Set) → F A → D
  F A = Set

-- Expected error: [MissingTypeSignature.Data]
-- Missing type signature for data definition D
-- when scope checking the declaration
--   data D where
--     c : (A : Set) → F A → D
