-- Andreas, 2025-04-12, issue #7796
-- Do not print guardedness hint in termination error
-- when guardedness is explicitly switched off.

{-# OPTIONS --no-guardedness #-}

-- {-# OPTIONS -v tc.warning.termination:50 #-}

record U : Set where
  coinductive
  field out : U

u : U
u .U.out = u

-- Expecting error without --guardedness hint
-- error: [TerminationIssue]
-- Termination checking failed for the following functions:
--   u
-- Problematic calls:
--   u
