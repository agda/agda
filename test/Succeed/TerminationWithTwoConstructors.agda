{-# OPTIONS --termination-depth=2 #-}

module TerminationWithTwoConstructors where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

module PR8184 where
  -- Andreas, 2025-11-04, re PR #8184
  -- https://github.com/agda/agda/pull/8184#issuecomment-3487147737
  -- The heuristics "treat any increase in a diagonal of a loop as infinite is unsound"
  -- in the sense that it mislabels programs as non-terminating
  -- that were previously recognized as terminating programs.

  f : (x y z : Nat) → Nat
  g : (x x' y z : Nat) → Nat

  -- 0. going through g zero times decreases x
  -- 1. going through g once preserves x and y and decreases z
  -- 2. going through g twice or more often preserves x, decreases y and destroys z

  f (suc x) y (suc (suc z)) = g x x (suc y) z
  f _ _ _ = zero

  g x x' (suc y) z = g (suc x') x' y (suc z)
  g x x' y z = f x y z

  -- If we count the increase on z in g -> g as infinite then we lose case 1.

  -- Should termination-check.

---------------------------------------------------------------------------
-- Original test case

f : Nat -> Nat
f zero = zero
f (suc zero) = zero
f (suc (suc n)) with zero
... | m = f (suc n)

{- internal represenation

f : Nat -> Nat
f zero = zero
f (suc zero) = zero
f (suc (suc n)) = faux n zero

faux : Nat -> Nat -> Nat
faux n m = f (suc n)

-}

{- this type checks with --termination-depth >= 2
calls:

 f -> f_with (-2)
 f_with -> f (+1)

-}
