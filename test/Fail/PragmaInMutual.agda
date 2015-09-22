
-- Currently pragmas are not allowed in mutual blocks.
-- This might change.
module PragmaInMutual where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

mutual
  {-# BUILTIN NATURAL Nat #-}
  T : Set -> Set
  T A = A

