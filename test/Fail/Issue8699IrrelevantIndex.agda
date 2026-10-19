-- Andreas, 2026-08-27, issue #8699
-- Variant of test case by @bdrisc-ant attributed to Claude.
-- Termination checker wrongly accepts decent in irrelevant fields in dot patterns.

{-# OPTIONS --show-irrelevant #-}

data Nat : Set where
  zero : Nat
  suc : (n : Nat) → Nat

data ⊥ : Set where

data PseudoFin : .Nat → Set where
  fzero : .(m : Nat) → PseudoFin (suc m)

f : .(s : Nat) → PseudoFin s → ⊥
f .(suc m) (fzero m) = f m (fzero m)

boom : ⊥
boom = f (suc zero) (fzero zero)

-- Expected error: [TerminationIssue]
-- Termination checking failed for the following function:
--   f
-- Problematic call:
--   f m (fzero m)
