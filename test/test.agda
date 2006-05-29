
module test where

id : {A:Set} -> A -> A
id x = x

foo : {A:Set} -> A -> A -> {!!}
foo x y = id ?

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

(+) : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)
