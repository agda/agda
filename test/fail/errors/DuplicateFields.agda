
module DuplicateFields where

postulate X : Set

record D : Set where
  field x : X

d : X -> X -> D
d x y = record {x = x; x = y}

