data Unit : Set where
  unit : Unit

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

data Test : Set where
  map : (Unit → Maybe Test) → Test

-- Accepted:
foo : Test → Unit
foo-aux : Maybe Test → Unit
foo (map f) = foo-aux (f unit)
foo-aux nothing = unit
foo-aux (just x) = foo x

test : Test → Unit
test (map f) with f unit
test (map f) | nothing = unit
test (map f) | just x = test x

-- WAS: Termination checker complains
-- SHOULD: succeed
