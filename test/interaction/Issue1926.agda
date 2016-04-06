module _ (A : Set) where

record R : Set where
  field f : A

test : R → R
test r = {!r!}
