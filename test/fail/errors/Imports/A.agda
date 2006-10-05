
module A where

postulate A : Set

-- Since it's in test/fail/... it has to fail when run by itself. The .flags
-- contains --proof-irrelevance.
data Two : Prop where
  one : Two
  two : Two

