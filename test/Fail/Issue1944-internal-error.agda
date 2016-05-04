-- Andreas, AIM XXIII, 2016-04-23
-- Issue 1944
-- Milestone 2.0: overload projection by fields (does not affect matching)

-- {-# OPTIONS -v tc.lhs.split:20 #-}

record R : Set2 where
  field out : Set1

r : R
R.out r = Set

s = r

open R r  -- fully applied open
open R
open R s

-- Now out is overloaded.  It is both a field and a projection.
-- We can still use it in pattern position (since a field does not make sense here).

ok : R
out ok = Set  -- out should be highlighted as projection

test : R → R
test x = out x  --  Was: internal error
