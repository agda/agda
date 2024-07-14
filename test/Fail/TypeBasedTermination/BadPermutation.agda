-- Tests bad combination of arguments
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.BadPermutation where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

foo : Nat → Nat → Nat
foo m (suc n) = foo n m
foo m zero    = foo zero m
