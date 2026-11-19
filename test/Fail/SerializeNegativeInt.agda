-- Andreas, 2026-11-19, regression from PR #7565
-- Negative Ints were not restored correctly from interface files,
-- breaking display forms with a negative number of pattern variables.

module SerializeNegativeInt where

open import SerializeNegativeInt.A

postulate
  P : M.D → Set
  p : P M.c

test : Set
test = p

-- Expected error mentions:
--
--   P c
--
-- (not P N.c).
