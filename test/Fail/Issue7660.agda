-- Andreas, 2025-04-19, issue #7660
-- Report and test case by Jesper
-- Display unsolved constraint for ambiguous constructor

-- {-# OPTIONS --allow-unsolved-metas #-} -- does not print constraints

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat

data D1 : Set where
  c : Bool → D1

data D2 : Set where
  c : Nat → D2

test : _ → Set
test (c x) = {!   !}

test2 : _
test2 = c {!   !}

-- Expected error: [UnsolvedConstraints]
-- Failed to solve the following constraints:
--   _18 := ambiguous constructor c ? : _9 (blocked on _9)
--   Check definition of test : _7 → Set
--     stuck because
--      LOCATION: error: [SplitError.BlockedType]
--       Cannot split on argument of unresolved type _7
--       when checking that the pattern c x has type _7
--     (blocked on _7)
