module Issue7836 where

record R : Set₁ where
  field f : Set

r : R
r = record where
      postulate f : Set
