-- Andreas, 2020-06-16, issue #4752
-- Disallow @-patterns in pattern synonyms.
--
-- Agda 2.5.2 implemented @-patterns and accidentially
-- allowed them in pattern synonyms.
-- However they just lead to a panic when used.

data Nat : Set where
  suc : Nat → Nat

pattern ss x = suc x@(suc _)

-- EXPECTED:
--
-- @-patterns are not allowed in pattern synonyms
-- when scope checking the declaration
--   pattern ss x = suc x@(suc _)

test : Nat → Set
test (ss x) = test x

-- WAS (from 2.5.2):
--
-- Panic: unbound variable x
-- when checking that the expression x has type Nat
