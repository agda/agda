-- Andreas, 2024-07-23
-- Trigger error TooManyPatternsInWithClause

f : Set₁
f with Set
f {Set} | _ = Set

-- Too many arguments given in with-clause
-- when checking that the clause
-- f with Set
-- f {Set} | _ = Set
-- has type Set₁
