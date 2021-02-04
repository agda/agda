{-# OPTIONS --allow-unsolved-metas #-}

postulate
  A : Set
  B : A → Set

variable
  a : A

D : B a → Set _

-- Expected: Warning about missing definition
-- Not expected: Complaint about generalizable variable
