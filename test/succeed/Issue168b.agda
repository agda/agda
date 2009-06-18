module Issue168b where

data Nat : Set where
  zero : Nat 
  suc  : Nat → Nat

module Membership (A : Set) where

  id : Nat → Nat
  id zero     = zero
  id (suc xs) = suc (id xs)
