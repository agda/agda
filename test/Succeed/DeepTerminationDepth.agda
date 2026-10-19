-- Andreas, 2025-11-01
-- Examples that termination-checked slowly with high termination depth.
-- Fast thanks to iterative deepening.

{-# OPTIONS --termination-depth=1000 #-}

-- {-# OPTIONS -v debug.time:100 -v term:3 #-}
-- {-# OPTIONS -v term.matrices:40 #-}

open import Agda.Builtin.Nat

postulate
  ANY : Nat

-- Dummy function to start termination timer for f
dummy : Nat → Nat
dummy (suc n) = dummy n
dummy zero = zero

-- extracted from the standard library Data.Nat.DivMod
module DivMod where

  f : (acc k m n o p : Nat) → Nat
  f acc k (suc m) (suc n) (suc o) (suc p) = f acc       (suc k) m   n o   p
  f acc k (suc m) (suc n) o       0       = f (suc acc) 0       ANY n ANY k
  f acc k m n o p = 0

module Mutual where

  f : Nat → Nat → Nat
  g : Nat → Nat → Nat

  f (suc x) (suc y) = g x y
  f _ _ = zero

  g (suc x) y = g x (suc y)
  g x (suc y) = f (suc x) y
  g _ _ = zero
