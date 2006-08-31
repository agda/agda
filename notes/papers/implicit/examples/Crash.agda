
module Crash where

data N : Set where
  zero : N
  suc  : N -> N

data B : Set where
  true : B
  false : B

F : B -> Set
F true  = N
F false = B

not : B -> B
not true  = false
not false = true

h : ((x : F _) -> F (not x)) -> N
h g = g zero

