-- Andreas, 2017-08-14, issue #2682, test case by Ulf

-- WAS: CheckInternal treats abstract projections as not in scope,
-- while the type checker allows them.

-- Adapted solution: allow also in CheckInternal

-- {-# OPTIONS -v tc.rec.proj:20 #-}
-- {-# OPTIONS -v tc.deftype:25 #-}
-- {-# OPTIONS -v tc:20 #-}

abstract
  record R : Set₁ where
    field X : Set

works : R → Set
works r = R.X r

test : R → Set
test r = {!R.X r!}

-- WAS: On give:
-- Expected non-abstract record type, found R
-- when checking that the expression R.X r has type Set

test2 : R → Set
test2 r = {! r .X !}
  where open R
