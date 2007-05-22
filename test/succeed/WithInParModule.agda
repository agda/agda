module WithInParModule where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Bool : Set where
  true : Bool
  false : Bool

isZero : Nat -> Bool
isZero zero = true
isZero (suc _) = false

module Foo (A : Set) where

  f : Nat -> Nat
  f n with isZero n
  f n | true = zero
  f n | false = suc zero
