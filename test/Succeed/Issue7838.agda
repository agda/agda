module Issue7838 where

record R : Set₂ where
  field f : Set₁

v : R
v = record where
      f = Set

r : R
r = record where
  module M = R v using (f)
  open M
