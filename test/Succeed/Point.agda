
module Point where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

record Point : Set where
  field
    x : Nat
    y : Nat

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

open Point renaming (x to getX; y to getY)

<_,_> : Nat -> Nat -> Point
< x , y > = record { x = x; y = y }

η : (p : Point) -> p == record { x = getX p; y = getY p }
η p = refl

swap : Point -> Point
swap p = < getY p , getX p >

swap-idem : (p : Point) -> swap (swap p) == p
swap-idem p = refl

