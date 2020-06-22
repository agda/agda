-- Andreas, 2020-05-08, issue #4637
-- Print record pattern (in with-function) in termination error.

-- {-# OPTIONS -v reify:60 #-}

record R : Set where
  pattern; inductive
  field foo : R

postulate
  bar : R → R

test : R → R
test r with bar r
test r | record { foo = x } with bar x
test r | record { foo = x } | _ = test x

-- WAS:
-- Termination checking failed for the following functions:
--   test
-- Problematic calls:
--   test r | bar r
--   Issue4637.with-14 r (recCon-NOT-PRINTED x)
--   | bar x
--   test x

-- EXPECTED:
-- Termination checking failed for the following functions:
--   test
-- Problematic calls:
--   test r | bar r
--   Issue4637.with-14 r (record { foo = x })
--   | bar x
--   test x
