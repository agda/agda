-- This file is imported by other tests, can't just remove (Andreas, 2015-07-15).

module Nat where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat
