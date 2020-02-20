module Issue4267.B where

open import Issue4267.A0

postulate
  X : Set

-- Crucial for bug: omitting signature of ra,
-- letting Agda infer its type.
ra = record {A = X}
