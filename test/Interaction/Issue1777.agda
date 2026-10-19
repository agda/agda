-- Andreas, 2016-02-16, issue 1777, reported by Martin Stone Davis

data D : Set where
  c : D

record R : Set where
  field f : D

test : R → D
test record { f = x } with x
... | y = {!y!}

-- Splitting on y should give
-- test record { f = x } | c = ?

-- Jesper, 2019-11-21, new output:
-- ... | c = ?
