
module Lib.Nat where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat  #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

_+_ : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)

{-# BUILTIN NATPLUS _+_ #-}
