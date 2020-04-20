-- Andreas, 2020-03-27, issue #3684
-- Warn about invalid fields instead of hard error.

module TooManyFields where

postulate X : Set

record D : Set where
  field x : X

d : X -> D
d x = record {x = x; y = x}
