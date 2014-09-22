{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --termination-depth=2  #-}

module _ where

open import Common.Prelude

module A where

  mutual

    f : Nat → Nat
    f zero = zero
    f (suc zero) = suc zero
    f (suc (suc x)) = g x

    g : Nat → Nat
    g x = f (suc ?)

  -- This should not fail termination checking,
  -- as ? := x is a terminating instance.

module B where

  mutual

    f : Nat → Nat
    f zero = zero
    f (suc zero) = suc zero
    f (suc (suc x)) = g ?

    g : Nat → Nat
    g x = f (suc x)

  -- This should not fail termination checking,
  -- as ? := x is a terminating instance.

