module Squash where

data _==_ {A : Set}(a : A) : A -> Set where
  refl : a == a

data Wrap (A : Set) : Set where
  wrap : A -> Wrap A

data Squash (A : Set) : Set where
  squash : .A -> Squash A

postulate
  A : Set
  a1 a2 : A

irr : squash a1 == squash a2
irr = refl

