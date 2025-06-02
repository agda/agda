-- Andreas, 2025-06-02, hint towards --guardedness even with --sized-types

{-# OPTIONS --sized-types #-}  -- just to trigger the right error message

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A

open Stream

repeat : ∀ {A} → A → Stream A
repeat x .head = x
repeat x .tail = repeat x

-- Expected error: [TerminationIssue]
-- Termination checking failed for the following functions:
-- (Option --guardedness might fix this problem, but it is not --safe
-- to use with --sized-types.)
--   repeat
-- Problematic calls:
--   repeat x
