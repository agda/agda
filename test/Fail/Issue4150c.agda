-- Andreas, 2026-02-28, issue #4150
-- Prefer MissingTypeSignature error over NotInScope error.

mutual
  R' = R
  record R where
    field f : Set

-- Expected error: [MissingTypeSignature.Record]
-- Missing type signature for record definition R
-- when scope checking the declaration
--   record R where
--     field f : Set
