
module TooFewFields where

postulate X : Set

record D : Set where
  x : X

d : D
d = record {}

