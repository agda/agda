-- Andreas, 2026-08-21, report, bisection, and test by Nisse
-- Regression introduced by #8602

{-# OPTIONS --without-K #-}

abstract

  data D : Set where
    c : D → D

  F : D → Set
  F (c x) = F x

-- Should termination check.
