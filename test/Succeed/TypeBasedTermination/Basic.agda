-- Basic functionality test
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}

module TypeBasedTermination.Basic where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

add : Nat → Nat → Nat
add x y = x
