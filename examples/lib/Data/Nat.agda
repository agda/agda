{-# OPTIONS --no-termination-check #-}

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

infix 40 _==_ _<_ _≤_ _>_ _≥_
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

_^_ : Nat -> Nat -> Nat
n ^ zero  = 1
n ^ suc m = n * n ^ m

_! : Nat -> Nat
zero  ! = 1
suc n ! = suc n * n !

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATMINUS _-_ #-}
{-# BUILTIN NATTIMES _*_ #-}

_==_ : Nat -> Nat -> Bool
zero  == zero  = true
zero  == suc _ = false
suc _ == zero  = false
suc n == suc m = n == m

_<_ : Nat -> Nat -> Bool
n     < zero  = false
zero  < suc m = true
suc n < suc m = n < m

_≤_ : Nat -> Nat -> Bool
n ≤ m = n < suc m

_>_ = flip _<_
_≥_ = flip _≤_

{-# BUILTIN NATEQUALS _==_ #-}
{-# BUILTIN NATLESS   _<_  #-}

divSucAux : Nat -> Nat -> Nat -> Nat -> Nat
divSucAux k m zero    j       = k
divSucAux k m (suc n) zero    = divSucAux (suc k) m n m
divSucAux k m (suc n) (suc j) = divSucAux k m n j

modSucAux : Nat -> Nat -> Nat -> Nat -> Nat
modSucAux k m zero    j       = k
modSucAux k m (suc n) zero    = modSucAux zero m n m
modSucAux k m (suc n) (suc j) = modSucAux (suc k) m n j

{-# BUILTIN NATDIVSUCAUX divSucAux #-}
{-# BUILTIN NATMODSUCAUX modSucAux #-}

div : Nat -> Nat -> Nat
div n  zero   = zero
div n (suc m) = divSucAux zero m n m

mod : Nat -> Nat -> Nat
mod n  zero   = zero
mod n (suc m) = modSucAux zero m n m

gcd : Nat -> Nat -> Nat
gcd a 0 = a
gcd a b = gcd b (mod a b)

lcm : Nat -> Nat -> Nat
lcm a b = div (a * b) (gcd a b)

even : Nat -> Bool
even n = mod n 2 == 0

odd : Nat -> Bool
odd n = mod n 2 == 1

