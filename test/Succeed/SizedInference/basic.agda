-- Basic functionality test
{-# OPTIONS --no-double-check --type-based-termination #-}

module SizedInference.basic where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

add : Nat → Nat → Nat
add x y = x
