
module Parity where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ

_+_ : ℕ -> ℕ -> ℕ
n + zero  = n
n + suc m = suc (n + m)

_*_ : ℕ -> ℕ -> ℕ
n * zero  = zero
n * suc m = n * m + n

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}
{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}

data Parity : ℕ -> Set where
  itsEven : (k : ℕ) -> Parity (2 * k)
  itsOdd  : (k : ℕ) -> Parity (2 * k + 1)

parity : (n : ℕ) -> Parity n
parity  zero              = itsEven zero
parity (suc n)         with parity n
parity (suc .(2 * k))     | itsEven k = itsOdd k
parity (suc .(2 * k + 1)) | itsOdd  k = itsEven (k + 1)

⌊_/2⌋ : ℕ -> ℕ
⌊ n /2⌋            with parity n
⌊ .(2 * k)     /2⌋    | itsEven k = k
⌊ .(2 * k + 1) /2⌋    | itsOdd  k = k
