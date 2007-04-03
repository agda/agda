
module Test where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

module Q where
  module R where
    f : Nat -> Nat
    f n = suc n

module B (n : Nat) where
  open Q.R public
  q = f n

module Bz = B zero

postulate
  _==_ : {A : Set} -> A -> A -> Set
  refl : {A : Set}{x : A} -> x == x

