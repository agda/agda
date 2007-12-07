-- There was a bug where f (suc n) didn't reduce for neutral n.
module Issue26 where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat  #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

f : Nat -> Nat
f 0       = 0
f (suc n) = f n

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

lem : (n : Nat) -> f (suc n) == f n
lem n = refl

