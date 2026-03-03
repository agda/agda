-- Andreas, 2026-02-28, issue #4150
-- Prefer MissingTypeSignature error over NotInScope error.

mutual
  record Foo : Set₁ where
    field
      A : Set
      B : A → F A  -- WAS: Not in scope: F
  F A = Set        -- MissingTypeSignature here

-- Expected error: [MissingTypeSignature.Function]
-- Missing type signature for left hand side F A
-- when scope checking the declaration
--   F A = Set
