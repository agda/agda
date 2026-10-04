-- Andreas, 2026-10-03, issue #8171
-- Metas could not be solved with variables of strictly positive polarity,
-- even in strictly positive positions.

{-# OPTIONS --polarity #-}

postulate
  A : Set
  P : @++ Set → Set
  p : (@++ X : Set) → P X
  q : {@++ X : Set} (@++ x : P X) → Set

G : @++ Set → Set
G X = q (p X)

-- Function types: the domain is a negative position.

H : @- Set → Set
H X = q (p (X → A))

I : @++ Set → Set
I X = q (p (A → X))

-- Should succeed.
