-- Andreas, AIM XXXV, 2022-05-09, issue #5728
-- Give a proper error rather than crashing.

test : Set
test with Set
...

-- In Agda 2.6.1 we got "missing with clauses for test".
-- In Agda 2.6.2 this used to be an internal error.
-- In Agda 2.6.3 this was fixed to produce a proper error again:
-- The right-hand side can only be omitted if there is an absurd
-- pattern, () or {}, in the left-hand side.

-- Andreas, 2025-04-07, fix for issue #7759 changes error to:
-- Too few arguments given in with-clause
-- when checking that the clause
-- test with Set
-- test
-- has type Set
