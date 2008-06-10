module ForallForParameters where

data D (a : Set) : Set where
  d : a -> D a

data P a : D a -> Set where

codata C {a} x : P a x -> Set where
