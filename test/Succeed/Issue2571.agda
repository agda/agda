
module _ where

data N : Set where
  zero : N
  suc  : N → N

record P : Set where
  constructor p
  field fst : N
        snd : N

open P

-- f = λ z → z   internally
f : P → P
f z = p (fst z) (snd z)

-- This should also be λ z → z, but was not due to #2157.
g : P → P
g (p x y) = p x y
