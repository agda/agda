-- Andreas, 2026-08-29, issue #8696
-- Issue found by Claude and reported by bdrisc-ant

-- Same as Issue8696.agda, but the copied type is a record rather than a data
-- type, exercising the recClause branch of the occurrence analysis.

{-# OPTIONS --safe --without-K #-}

data ⊥ : Set where

module M (A : Set) where
  record Neg (X : Set) : Set where
    constructor mk
    field un : X → A

mutual
  module N = M ⊥

  G : Set → Set
  G = N.Neg

  -- This negative data type should be rejected.
  data D : Set where
    lam : G D → D

app : D → D → ⊥
app (lam f) d = N.Neg.un f d

delta : D
delta = lam (N.mk λ d → app d d)

Omega : ⊥
Omega = app delta delta
