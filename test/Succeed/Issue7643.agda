-- Andreas, 2025-01-02, issue #7643
-- WAS: Uncaught pattern violation when checking isFibrant in coverage checker.

{-# OPTIONS --allow-unsolved-metas #-}

data ⊥ : Set where

-- The sort of A is not determined here,
-- could e.g. be Set or Set1.

data Wrap (A : _) : Set1 where
  wrap : A → Wrap A

test : Wrap ⊥ → ⊥
test (wrap ())

-- Should succeed with unsolved metas.
