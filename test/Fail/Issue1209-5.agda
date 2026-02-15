{-# OPTIONS --safe #-}

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
-- Termination checking failed for the following function:
-- (Option --guardedness might fix this problem.)
--   repeat
-- Problematic call:
--   repeat x
