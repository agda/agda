-- Andreas, 2024-02-20, issue #7136:
-- Error out on unsupported pattern synonym arguments.

{-# OPTIONS --erasure #-}

open import Agda.Builtin.Nat

pattern p (@0 x) = suc x
-- Should be rejected: quantity attribute in pattern synonym not supported.

pred : Nat → Nat
pred (p x) = x
pred zero  = zero
