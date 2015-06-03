-- Andreas, 2013-03-22
module Issue473a where

data D : Set where
  d : D

data P : D → Set where
  p : P d

record Rc : Set where
  constructor c
  field f : D

-- Andreas, 2015-06-03, after unfixing Issue 473, this also fails:
works : {r : Rc} → P (Rc.f r) → Set
works p = D

works' : (r : Rc) → P (Rc.f r) → Set
works' (c .d) p = D

-- If we remove the constructor, the example fails:

record R : Set where
  field f : D

fails : {r : R} → P (R.f r) → Set
fails p = D

-- d != R.f r of type D
-- when checking that the pattern p has type P (R.f r)

-- The error is justified since there is no pattern we could write down
-- for r.  It would have to look like
--
--   record { f = .d }
--
-- but anonymous record patterns are not supported.
