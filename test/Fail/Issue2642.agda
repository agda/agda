-- Andreas, 2017-07-13, issue #2642

record R : Set₁ where
  field
    F : Set
    F : Set  -- duplicate field, should be rejected

-- Otherwise, this gives an internal error:

test : Set → R
test A = record{ F = A }
