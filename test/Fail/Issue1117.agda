-- Andreas, 2014-05-02
-- Epic issue by Nisse and Andrea Vezzosi

record R : Set₁ where
  field
    A : Set

postulate
  X : R
  x : R.A X

Y : R
Y = X

record S : Set where
  field
    G : R.A Y  -- Works if Y is replaced by X.

s : S
s = record { G = x }

-- This crashed epic with an internal error.

-- Expected behavior now: crash because main is missing.
