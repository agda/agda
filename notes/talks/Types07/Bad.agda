
module Bad where

data Bool : Set where
  false : Bool
  true  : Bool

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

F : Bool -> Set
F false = Bool
F true  = Nat

cast : {x : Bool} -> F x -> F x
cast a = a

not : Bool -> Bool
not true  = false
not false = true

oops : Bool
oops = not (cast zero)

