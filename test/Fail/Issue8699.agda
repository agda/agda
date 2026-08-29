-- Andreas, 2026-08-27, issue #8699
-- Reported and test case by @bdrisc-ant attributed to Claude
-- Termination checker wrongly accepts decent in irrelevant fields in dot patterns.

-- {-# OPTIONS -v tc.cc:20 #-}
-- {-# OPTIONS -v tc.inj.check:50 #-}
-- {-# OPTIONS -v tc.inj:50 #-}
-- {-# OPTIONS -v tc:20 #-}

{-# OPTIONS --show-irrelevant #-}

data Nat : Set where
  zero : Nat
  suc : (n : Nat) → Nat

data ⊥ : Set where

record SqNat : Set where
  constructor sq
  field .unsq : Nat

data PseudoFin : SqNat → Set where
  fzero : (m : Nat) → PseudoFin (sq (suc m))
  fsuc  : (m : Nat) → PseudoFin (sq m) → PseudoFin (sq (suc m))

f : (s : SqNat) → PseudoFin s → ⊥
f .(sq (suc m)) (fzero m)  = f (sq m) (fzero m)
f .(sq (suc m)) (fsuc m x) = f (sq m) (fsuc m x)
  -- WAS: Removing this case (and constructor fsuc) makes Agda loop

boom : ⊥
boom = f (sq (suc zero)) (fzero zero)

-- Expected error: [TerminationIssue]
-- Termination checking failed for the following function:
--   f
-- Problematic call:
--   f (sq m) (fsuc m x)
