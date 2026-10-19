-- Andreas, 2026-10-03, issue #8171
-- The occurs check must respect polarities when solving metas.

{-# OPTIONS --polarity #-}

postulate
  A : Set
  P : @++ Set → Set
  q : {@++ X : Set} (@++ x : P X) → Set
  r : (@- X : Set) → P (A → X)

-- The implicit argument of q would have to be solved by A → X,
-- but X is negative, so it may not appear in the codomain of
-- a function type in a strictly positive position.

bad : @- Set → Set
bad X = q (r X)
