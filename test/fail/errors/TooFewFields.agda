
module TooFewFields where

postulate X : Set

record D : Set where
  field x : X

d : D
d = record {}

