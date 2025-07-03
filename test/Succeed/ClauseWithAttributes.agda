-- Andreas, 2025-07-03
-- Attributes are not supported on function clauses.

{-# OPTIONS --erasure #-}

@0 id : (A : Set) → A → A
@0 id A x = x

-- Deadcode warning expected.
