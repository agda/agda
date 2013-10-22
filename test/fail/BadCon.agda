module BadCon where

data D : Set where
  d : D

data E : Set where
  d : E

postulate
  F : D -> Set

test : (x : D) -> F x
test = d

-- Bad error (unbound de Bruijn index):
-- the constructor d does not construct an element of F @0
-- when checking that the expression d has type (x : D) → F x
