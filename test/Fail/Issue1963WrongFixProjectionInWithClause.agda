-- Andreas, 2016-07-20

-- With clauses should follow the parent clause
-- what copattern style (prefix/postfix) concerns.

record R : Set₂ where
  field f : Set₁

test : R
test .R.f with R    -- post-fix here
R.f test | _ = Set  -- pre-fix there

-- That's not nice, thus, it is an error.
