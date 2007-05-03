
module TooManyFields where

postulate X : Set

record D : Set where
  x : X

d : X -> D
d x = record {x = x; y = x}

