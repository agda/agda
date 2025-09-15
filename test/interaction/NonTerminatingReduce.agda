-- Testcase by Ulf Norell (2014-07-07, commit c8128d1).
-- Revised by Andreas 2025-09-15 for issue #2410.

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

pred : Nat → Nat
pred zero = zero
pred (suc n) = n

-- The following function is actually terminating (even at compile-time)
-- but we label it as NON_TERMINATING for the sake of this test case.
{-# NON_TERMINATING #-}
loop : Nat → Nat
loop zero = zero
loop n = loop (pred n)

hole : Set
hole = {!!}

-- Non-terminating functions do not reduce by default (C-c C-n),
-- only when more force is applied (C-u C-c C-n).
