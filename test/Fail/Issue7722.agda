-- Andreas, 2025-02-28, issue #7722
-- Reported by decorator-factory, test shrunk by Andreas.
--
-- The pattern parser took exponential time when non-pattern operators
-- were mentioned in the pattern.
-- These were both interpreted as pattern variables and operators,
-- so for n occurrences of this operator 2^n parse trees were produced.
-- Only one of them constitutes a valid pattern, but the pattern
-- validity check had to go through all the products in a parse tree.
--
-- This is fixed by only considering operators that are constructors or pattern synonyms.

postulate
  _+_ : Set → Set → Set

infixl 42 _+_

test : Set → Set
test x :=  -- typo := instead of =
  x + x + x + x +
  x + x + x + x +
  x + x + x + x +
  x + x + x + x +
  x + x + x + x +
  x + x + x + x +
  x + x + x + x +
  x + x + x + x +
  x + x + x + x +
  x + x + x + x +
  x

-- WAS: OOM
-- NOW: Should fail fast.
