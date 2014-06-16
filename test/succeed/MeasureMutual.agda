-- In a mutual block, either all or none must have a MEASURE declaration.

module _ where

open import Common.Prelude

mutual

  {-# MEASURE n #-}
  f : (n : Nat) → Nat
  f zero = zero
  f (suc n) = g n

  {-# MEASURE n #-}
  g : (n : Nat) → Nat
  g zero = zero
  g (suc n) = suc (f n)

