-- Andreas, 2013-03-22
module Issue473a where

data D : Set where
  d : D

data P : D → Set where
  p : P d

record Rc : Set where
  constructor c
  field f : D

works : {r : Rc} → P (Rc.f r) → Set
works p = D

works' : (r : Rc) → P (Rc.f r) → Set
works' (c .d) p = D

-- We remove the constructor:

record R : Set where
  field f : D

test : {r : R} → P (R.f r) → Set
test p = D
