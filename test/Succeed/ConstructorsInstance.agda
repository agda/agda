module ConstructorsInstance where

record UnitRC : Set where
  constructor tt

record UnitR : Set where

data UnitD : Set where
  tt : UnitD

postulate
  fRC : {{_ : UnitRC}} → Set
  fR  : {{_ : UnitR}}  → Set
  fD  : {{_ : UnitD}}  → Set

tryRC : Set
tryRC = fRC

tryR : Set
tryR = fR

tryD : Set
tryD = fD
