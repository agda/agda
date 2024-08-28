-- Andreas, 2024-07-07, issue #6744, reported and testcase by Jesper.

-- Reduction needed in forcing analysis.

{-# OPTIONS --erasure #-}

-- {-# OPTIONS -v tc.force:60 #-}

open import Agda.Builtin.Nat

-- This alias fools the forcing analysis of Agda 2.6.4 and below:
suc' : Nat → Nat
suc' = suc

data D : Nat → Set where
  c : (@0 n : Nat) → D (suc' n)

foo : (n : Nat) → D n → Set
foo n (c _) = Nat

-- Should be accepted.
