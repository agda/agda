-- {-# OPTIONS -v term:20 #-}
module BadTermination where

data N : Set where
  zero : N
  suc  : N -> N

postulate inf : N

data D : N -> Set where
  d₁ : D (suc inf)
  d₂ : D inf

f : (n : N) -> D n -> N
f .inf       d₂ = zero
f .(suc inf) d₁ = f inf d₂
