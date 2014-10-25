module ConstructorsInstance where

record UnitRC : Set where
  instance
    constructor tt

data UnitD : Set where
  instance
    tt : UnitD

postulate
  fRC : {{_ : UnitRC}} → Set
  fD  : {{_ : UnitD}}  → Set

tryRC : Set
tryRC = fRC

tryD : Set
tryD = fD


data D : Set where
  a : D
  instance
    b : D
  c : D

postulate
  g : {{_ : D}} → Set

-- This should work because instance search will choose [b]
try2 : Set
try2 = g
