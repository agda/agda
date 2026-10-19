-- Andreas, 2026-08-29, issue #8696
-- Issue found by Claude and reported by bdrisc-ant

-- A data or record type copied by a module application inside an open mutual
-- block had its argument occurrences recomputed from the pattern-less clause
-- N.F = M.F ⊥, which made them all Unused, so a negative occurrence through
-- the copy went unnoticed.

{-# OPTIONS --safe --without-K #-}

data ⊥ : Set where

module M (A : Set) where
  data Neg (X : Set) : Set where
    neg : (X → A) → Neg X

mutual
  module N = M ⊥

  G : Set → Set
  G = N.Neg

  -- This negative data type should be rejected.
  data D : Set where
    lam : G D → D

-- The rest as usual:
-- we have a representation of untyped lambda calculus which is inconsistent through self-application.

pattern abs f = lam (N.neg f)

app : D → D → ⊥
app (abs f) = f

delta : D
delta = abs λ d → app d d

Omega : ⊥
Omega = app delta delta
