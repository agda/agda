-- Test a recursive call that uses a deeper pattern
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.DeepPatternMatching where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data Parity : Set where
  0ℙ : Parity
  1ℙ : Parity

parity : Nat → Parity
parity zero          = 0ℙ
parity (suc zero)    = 1ℙ
parity (suc (suc n)) = parity n
