-- {-# OPTIONS -v tc.pos:10 #-}
-- Andreas, 2014-07-04

record R (A : Set) : Set where
  no-eta-equality
  field f : R A

-- Should complain about missing 'inductive' or 'coinductive'.
