-- Andreas, 2019-04-12, issue #3684
-- Report also available record fields in case user gives spurious fields.

-- {-# OPTIONS -v tc.record:30 #-}

record R : Set₁ where
  field
    foo {boo} moo : Set

test : (A : Set) → R
test A = record
  { moo = A
  ; bar = A
  ; far = A
  }

-- The record type R does not have the fields bar, far but it would
-- have the fields foo, boo
-- when checking that the expression
-- record { moo = A ; bar = A ; far = A } has type R
