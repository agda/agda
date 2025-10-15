-- Testcase by Ulf (2014-07-07, commit c8128d1).
-- Revised by Andreas and Ulf 2025-09-16 for issue #2410.

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then a else b = a
if false then a else b = b

pred : Nat → Nat
pred zero = zero
pred (suc n) = n

-- The following function diverging for unknown n, so we need to label it NON_TERMINATING.
-- At run-time it terminates, so we might want to evaluate it on some concrete numbers.
{-# NON_TERMINATING #-}
loop : Nat → Nat
loop n = if n == 0 then 0 else loop (pred n)

hole : Set
hole = {!!}

-- Non-terminating functions do not reduce by default (C-c C-n),
-- only when more force is applied (C-u C-c C-n).
