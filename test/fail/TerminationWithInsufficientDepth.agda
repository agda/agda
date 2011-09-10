{-# OPTIONS --termination-depth=1 #-}

module TerminationWithInsufficientDepth where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

f : Nat -> Nat
f zero = zero
f (suc zero) = zero
f (suc (suc n)) with zero
... | m = f (suc n)

{- this type checks with --termination-depth >= 2
calls:

 f -> f_with (-2)
 f_with -> f (+1)

-}
