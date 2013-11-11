
module Issue59 where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

-- This no longer termination checks with the
-- new rules for with.
bad : Nat → Nat
bad n with n
... | zero  = zero
... | suc m = bad m
