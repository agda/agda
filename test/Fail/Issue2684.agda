-- Andreas, 2017-08-13, issue #2684
-- Better error for abstract constructor.

abstract
  data D : Set where
    c : D

  data E : Set where
    c : E

test : D
test = c

-- Expected:
-- Constructor c is abstract, thus, not in scope here
-- when checking that the expression c has type D
