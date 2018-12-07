{-# OPTIONS -WnoMissingDefinitions #-}

postulate
  A : Set
  B : A → Set

variable
  a : A

data D : B a → Set

-- Expected: Warning about missing definition
-- Not expected: Complaint about generalizable variable
