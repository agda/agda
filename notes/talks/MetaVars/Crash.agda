
module Crash where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Bool : Set where
  true : Bool
  false : Bool

F : Bool -> Set
F true  = Nat
F false = Bool

not : Bool -> Bool
not true  = false
not false = true

h : ((x : F ?) -> F (not x)) -> Nat
h g = g zero

