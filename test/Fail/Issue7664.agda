-- Andreas, 2026-09-02, issue #7664
-- Report and test case by Amelia Liao.

module Issue7664 where

module X (A : Set1) where
  data D : Set1 where
    c : A → D

module _ (B : Set) where
  open X Set         renaming (D to D ; c to c )
  open X (Set → Set) renaming (D to D'; c to c')

  f : D → Set1
  f (c' x) = Set

-- Expected error: [UnequalTerms]
-- The terms
--   Set → Set
-- and
--   Set
-- are not equal at type Set₁
-- when checking that the pattern c' x has type D
