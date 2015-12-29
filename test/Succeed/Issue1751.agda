-- Andreas, 2015-12-29
-- with-clause stripping for record patterns

-- {-# OPTIONS -v tc.with.strip:60 #-}

record R : Set1 where
  field
    f : Set

test : R → Set1
test record{ f = a } with a
... | x = R

test1 : R → Set1
test1 record{ f = a } with a
test1 record{ f = a } | _ = R

test2 : R → Set1
test2 record{ f = a } with a
test2 record{ f = _ } | _ = R

-- Visible fields may be missing.
test3 : R → Set1
test3 record{ f = a } with a
test3 record{} | _ = R

-- With-clauses may specify more fields than the parent
test4 : R → Set1
test4 record{} with R
test4 record{ f = _ } | _ = R

-- all should pass
