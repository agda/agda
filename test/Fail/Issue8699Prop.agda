-- Andreas, 2026-08-27, issue #8699
-- Reported and test case by @bdrisc-ant attributed to Claude
-- Termination checker wrongly accepts decent in Prop-sorted subterms in dot patterns.

{-# OPTIONS --prop #-}
{-# OPTIONS --show-irrelevant #-}

data ⊥ : Set where

data Nat : Prop where
  zero : Nat
  suc : (n : Nat) → Nat

record SqNat : Set where
  constructor sq
  field unsq : Nat

data PseudoFin : SqNat → Set where
  fzero : (m : Nat) → PseudoFin (sq (suc m))
  -- fsuc  : (m : Nat) → PseudoFin (sq m) → PseudoFin (sq (suc m))

f : (s : SqNat) → PseudoFin s → ⊥
f .(sq (suc m)) (fzero m)  = f (sq m) (fzero m)
-- f .(sq (suc m)) (fsuc m x) = f (sq m) (fsuc m x)
  -- WAS: Removing this case (and constructor fsuc) makes Agda loop in the injectivity test

boom : ⊥
boom = f (sq (suc zero)) (fzero zero)

-- f should not termination check

-- Expected error: [TerminationIssue]
-- Termination checking failed for the following function:
--   f
-- Problematic call:
--   f (sq m) (fzero m)
