module Issue589 where

data N : Set where
  zero : N
  suc : N -> N

_+_ : N -> N -> N
zero + y = y
suc x + y = suc ?
