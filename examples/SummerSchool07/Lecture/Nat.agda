
module Nat where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

infixl 60 _+_
infixl 70 _*_

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

