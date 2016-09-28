-- Andreas, 2016-07-20, issue #2100 termination and where

data D : Set where
  pair : (x y : D) → D

works : (p q : D) → D
works (pair a b) (pair c d) = pair
  (works a (pair c d))
  (works (pair a b) c)

-- If we abstract out the two calls with where
-- termination check fails.

fails : (p q : D) → D
fails (pair a b) (pair c d) = pair u v
  where
  u = (fails a (pair c d))
  v = (fails (pair a b) c)

-- Would be nice if this succeeded.
-- (Ideally before the year 2100.)
