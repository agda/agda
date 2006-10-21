
module Data.Nat where

import Prelude
import Data.Bool as Bool

open Prelude
open Bool

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN SUC suc #-}
{-# BUILTIN ZERO zero #-}

infix 40 _==_ _<_
infixl 60 _+_ _-_
infixl 70 _*_
infixr 80 _^_
infix 100 _!

_+_ : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)

_-_ : Nat -> Nat -> Nat
zero  - m     = zero
suc n - zero  = suc n
suc n - suc m = n - m

_*_ : Nat -> Nat -> Nat
zero  * m = zero
suc n * m = m + n * m

div2 : Nat -> Nat
div2  zero         = 0
div2 (suc  zero)   = 0
div2 (suc (suc n)) = suc (div2 n)

mod2 : Nat -> Nat
mod2  zero         = 0
mod2 (suc zero)    = 1
mod2 (suc (suc n)) = mod2 n

_^_ : Nat -> Nat -> Nat
n ^ zero  = 1
n ^ suc m = n * n ^ m

_! : Nat -> Nat
zero  ! = 1
suc n ! = suc n * n !

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATMINUS _-_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATDIV2 div2 #-}
{-# BUILTIN NATMOD2 mod2 #-}

private
  primitive
    primNatDivSuc : Nat -> Nat -> Nat
    primNatModSuc : Nat -> Nat -> Nat

div : Nat -> Nat -> Nat
div n  zero   = zero
div n (suc m) = primNatDivSuc n m

mod : Nat -> Nat -> Nat
mod n  zero   = zero
mod n (suc m) = primNatModSuc n m

gcd : Nat -> Nat -> Nat
gcd a 0 = a
gcd a b = gcd b (mod a b)

lcm : Nat -> Nat -> Nat
lcm a b = div (a * b) (gcd a b)

_==_ : Nat -> Nat -> Bool
zero	== zero  = true
zero	== suc _ = false
suc _ == zero  = false
suc n == suc m = n == m

_<_ : Nat -> Nat -> Bool
n     < zero  = false
zero  < suc m = true
suc n < suc m = n < m

_≤_ : Nat -> Nat -> Bool
n ≤ m = n < m || n == m

_>_ = flip _<_
_≥_ = flip _≤_

even : Nat -> Bool
even n = mod2 n == 0

odd : Nat -> Bool
odd n = mod2 n == 1

_≡_ : Nat -> Nat -> Set
n ≡ m = IsTrue (n == m)

{-# BUILTIN NATEQUALS _==_ #-}
{-# BUILTIN NATLESS   _<_  #-}

