-- 2014-01-01 Andreas, test case constructed by Christian Sattler

{-# OPTIONS --allow-unsolved-metas #-}

-- unguarded recursive record
record R : Set where
  eta-equality
  inductive
  constructor cons
  field
    r : R


postulate F : (R → Set) → Set

q : (∀ P → F P) → (∀ P → F P)
q h P = h (λ {(cons x) → {!!}})

-- ISSUE WAS: Bug in implementation of eta-expansion of projected var,
-- leading to loop in Agda.
