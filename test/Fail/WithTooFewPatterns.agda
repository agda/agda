-- Trigger error TooFewPatternsInWithClause

test : Set → Set
test A with A
test | B = B

-- Too few arguments given in with-clause
-- when checking that the clause
-- test A with A
-- test | B = B
-- has type Set → Set
