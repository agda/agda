module Issue7837 where

record R : Set₂ where
  field f : Set₁

v : R
v = record where
      f = Set

r1 : R
r1 = record where
       open R v using (f) renaming (f to f)
