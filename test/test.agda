
module test where

module List (A:Set) where

  data List : Set where
    nil  : List
    (::) : A -> List -> List

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

module ListNat = List Nat
open ListNat

