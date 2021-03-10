{-# OPTIONS -v tc.conv.fun:20 #-}

-- Andreas, 2019-11-06, issue #4175, reported and test case by nad.
-- Check quantity for function type subtyping.

postulate
  F : Set → Set
  G : (@0 Set → Set) → Set

-- If an erased function is expected, we cannot pass one
-- that might actually use its arguments.

ShouldFail : Set
ShouldFail = G F

-- Note the eta-expanded version already failed:
-- Fails = G λ x → F x
