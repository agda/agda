
module Position where

open import Prelude
open import Star

data Bit : Set where
  low  : Bit
  high : Bit

data Edge {X : Set}(R : Rel X) : Rel (X × Bit) where
  next : {x y : X}{b : Bit} -> R x y -> Edge R (x , b) (y , b)
  edge : {x y : X} -> R x y -> Edge R (x , low) (y , high)

Pos : {X : Set}(R : Rel X) -> Rel (X × Bit)
Pos R = Star (Edge R)
