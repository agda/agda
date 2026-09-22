{-# OPTIONS -v treeless.opt:20 #-}
-- Test that inlining a recursive function doesn't throw
-- the compiler into a loop.
module _ where

open import Common.Prelude

f : Nat → Nat
f zero = zero
f (suc n) = f n
{-# INLINE f #-}

main : IO Unit
main = printNat (f 4)
