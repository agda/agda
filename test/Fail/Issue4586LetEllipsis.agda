-- Andreas, 2020-04-15, issue #4586
-- An unintended internal error.

test : Set₁
test = let ... | _ = Set
       in  Set

-- WAS:
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/Syntax/Translation/ConcreteToAbstract.hs:1417

-- EXPECTED:
-- Could not parse the left-hand side ... | _
-- Operators used in the grammar:
--   None
-- when scope checking let ... | _ = Set in Set
