{-# OPTIONS --termination-depth=1 #-}

module TerminationWithInsufficientDepth where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

module Depth2 where

  -- The fix to issue 59 makes this go through.
  -- f : Nat -> Nat
  -- f zero = zero
  -- f (suc zero) = zero
  -- f (suc (suc n)) with zero
  -- ... | m = f (suc n)

  -- Using a helper function, we still need termination-depth
  g : Nat → Nat → Nat
  f : Nat → Nat

  f zero = zero
  f (suc zero) = zero
  f (suc (suc n)) = g n zero

  g n m = f (suc n)

  {- this type checks with --termination-depth >= 2
  calls:

   f -> f_with (-2)
   f_with -> f (+1)

  -}

module Depth3 where

  f : Nat → Nat
  g : Nat → Nat

  f zero = zero
  f (suc zero) = zero
  f (suc (suc zero)) = zero
  f (suc (suc (suc n))) = g n

  g n = f (suc (suc n))
