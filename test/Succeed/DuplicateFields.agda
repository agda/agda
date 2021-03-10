-- Andreas, 2020-03-27, issue #3684
-- Warn about duplicate fields instead of hard error.

module DuplicateFields where

postulate X : Set

record D : Set where
  field x : X

d : X → X → D
d x y = record{ x = x; x = y }
