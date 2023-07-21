-- Andreas, 2023-06-10, issue #6687, reported and test case by Marvin Meller.
-- Regression in 2.6.1 introduced by PR #4424 fixing issue #906.
-- Not fixed in #5065 which reported a similar problem.

open import Agda.Builtin.Nat

data Vect {ℓ} (A : Set ℓ) : Nat → Set ℓ where
  nil  : Vect A 0
  cons : (n : Nat) → A → Vect A n → Vect A (suc n)

data Val (n : Nat) : Set where
  vclos : (m : Nat) → Vect (Val n) m → Val n

-- Problem was:
-- The termination checker reduced the rhs of clause 1 with clause 2.
-- Clause 2 was incorrectly labeled exact because it is CATCHALL.
-- Issue is fixed by not labeling CATCHALL clauses as exact,
-- and thus preventing to reduce with them in the termination checker.

bad : (n : Nat) → Val n → Val n
bad n v@(vclos _ (cons _ _ _)) = bad n v
{-# CATCHALL #-}
bad _ (vclos _ vs) = vclos _ vs

-- Expected error:
--
-- Termination checking failed for the following functions:
--   bad
-- Problematic calls:
--   bad n (vclos (suc n₁) (cons n₁ x x₁))
