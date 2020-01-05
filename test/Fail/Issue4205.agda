-- Andreas, 2019-12-03, issue #4205, reported by Smaug123,
-- first shrinking by Jesper Cockx

record R : Set₂ where
  field
    f : Set₁

postulate
  r : R

open R r

test : R
R.f test with Set₃
f test | _  = Set

-- WAS: internal error in getOriginalProjection

-- EXPECTED:
-- With clause pattern f is not an instance of its parent pattern R.f
-- when checking that the clause
-- R.f test with Set₃
-- f test | _ = Set
-- has type R
