module Point where

open import Nat
open import Bool

-- A record can be seen as a one constructor datatype. In this case:
data Point' : Set where
  mkPoint : (x : Nat)(y : Nat) -> Point'

getX : Point' -> Nat
getX (mkPoint x y) = x

getY : Point' -> Nat
getY (mkPoint x y) = y
