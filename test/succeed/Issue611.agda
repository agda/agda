-- Andreas, 2012-04-18
module Issue611 where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Bool : Set where
  true false : Bool

T : Bool -> Set
T true  = {x : Bool} -> Nat
T false = {x : Bool} -> Bool

data D (b : Bool) : Set where
  c : T b -> D b

d : D false
d = c {_} true
