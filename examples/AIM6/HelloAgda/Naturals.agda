
module Naturals where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

infixl 60 _+_
infixl 80 _*_

_+_ : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)

_*_ : Nat -> Nat -> Nat
zero  * m = zero
suc n * m = m + n * m

{-# BUILTIN NATURAL  Nat  #-}
{-# BUILTIN ZERO     zero #-}
{-# BUILTIN SUC      suc  #-}
{-# BUILTIN NATPLUS  _+_  #-}
{-# BUILTIN NATTIMES _*_  #-}
