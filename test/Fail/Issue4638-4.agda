{-# OPTIONS --erasure #-}

open import Agda.Builtin.Bool

data D : Set where
  run-time        : D
  @0 compile-time : D

-- This code should be rejected: Both f compile-time and f run-time
-- are type-correct run-time terms.

f : @0 D → Bool
f compile-time = true
f run-time     = false
