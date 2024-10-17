-- The usage of sized type within a non-sized type should be fine
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.Nonsized where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data K : Set where
  k : Nat → K

data K2 (n : Nat) : Set where
  k2 : K2 n
