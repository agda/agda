
module Parity where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

_+_ : Nat -> Nat -> Nat
n + zero  = n
n + suc m = suc (n + m)

_*_ : Nat -> Nat -> Nat
n * zero  = zero
n * suc m = n * m + n

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}
{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}

data Parity : Nat -> Set where
  itsEven : (k : Nat) -> Parity (2 * k)
  itsOdd  : (k : Nat) -> Parity (2 * k + 1)

parity : (n : Nat) -> Parity n
parity  zero              = itsEven zero
parity (suc n)         with parity n
parity (suc .(2 * k))     | itsEven k = itsOdd k
parity (suc .(2 * k + 1)) | itsOdd  k = itsEven (k + 1)

half : Nat -> Nat
half n         with parity n
half .(2 * k)     | itsEven k = k
half .(2 * k + 1) | itsOdd  k = k

