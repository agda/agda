{-# OPTIONS --without-K #-}

module Issue1680 where

data Nat : Set where
  Z : Nat
  S : Nat → Nat

record Nat2Nat : Set where
  field fun : Nat → Nat
open Nat2Nat

zero : Nat2Nat
zero .fun Z    = Z
zero .fun (S n) = zero .fun n

record Nat2Nat2 : Set where
  field step : Nat → Nat → Nat
open Nat2Nat2

add : Nat2Nat2
add .step Z m = m
add .step (S n) m = S (add .step n m)
