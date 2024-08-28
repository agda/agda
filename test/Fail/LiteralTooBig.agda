-- Andreas, 2024-07-22
-- Trigger error LiteralTooBig

open import Agda.Builtin.Nat

test : Nat → Set
test 42 = Nat
test _  = Nat

-- Expected error:
-- Matching on natural number literals is done by expanding the
-- literal to the corresponding constructor pattern, so you probably
-- don't want to do it this way
-- when checking that the pattern 42 has type Nat
