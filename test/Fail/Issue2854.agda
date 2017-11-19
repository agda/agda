-- Andreas, 2017-11-19, issue #2854

-- Agda should not complain about "possibly empty type of sizes"
-- if the SIZELT builtin is not bound.

data Tree : Set₁ where
  node : {A : Set} (f : A → Tree) → Tree

const : Tree → Tree
const t = node λ x → t

-- WAS:
-- Failed to solve the following constraints:
--   Is not empty type of sizes: _A_6 t

-- Expected:
-- Unsolved meta.
