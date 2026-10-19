-- Andreas, 2026-02-28, issue #4150
-- Prefer MissingTypeSignature error over NotInScope error.

mutual
  data D : Set₁ where
    c : (A : Set) → F A → D
  F A = Set

-- Expected error: [MissingTypeSignature.Function]
-- Missing type signature for left hand side F A
-- when scope checking the declaration
--   F A = Set
