{-# OPTIONS --termination-depth=2 #-}

module TerminationWithTwoConstructors where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

f : Nat -> Nat
f zero = zero
f (suc zero) = zero
f (suc (suc n)) with zero
... | m = f (suc n)

{- internal represenation

f : Nat -> Nat
f zero = zero
f (suc zero) = zero
f (suc (suc n)) = faux n zero

faux : Nat -> Nat -> Nat
faux n m = f (suc n)

-}

{- this type checks with --termination-depth >= 2
calls:

 f -> f_with (-2)
 f_with -> f (+1)
 
-}