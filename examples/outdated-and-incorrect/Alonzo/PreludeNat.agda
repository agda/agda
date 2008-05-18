module PreludeNat where
open import AlonzoPrelude
import PreludeBool as Bool

open Bool

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

_^_ : Nat -> Nat -> Nat
n ^ zero  = 1
n ^ suc m = n * n ^ m

_! : Nat -> Nat
zero  ! = 1
suc n ! = suc n * n !

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATMINUS _-_ #-}
{-# BUILTIN NATTIMES _*_ #-}

divSuc : Nat -> Nat -> Nat
divSuc  zero   _ = zero
divSuc (suc n) m = 1 + divSuc (n - m) m

modSuc : Nat -> Nat -> Nat
modSuc  zero   _ = zero
modSuc (suc n) m = modSuc (n - m) m

{-# BUILTIN NATDIVSUC divSuc #-}
{-# BUILTIN NATMODSUC modSuc #-}

div : Nat -> Nat -> Nat
div n  zero   = zero
div n (suc m) = divSuc n m

mod : Nat -> Nat -> Nat
mod n  zero   = zero
mod n (suc m) = modSuc n m

gcd : Nat -> Nat -> Nat
gcd a 0 = a
gcd a b = gcd b (mod a b)

lcm : Nat -> Nat -> Nat
lcm a b = div (a * b) (gcd a b)

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

even : Nat -> Bool
even n = mod n 2 == 0

odd : Nat -> Bool
odd n = mod n 2 == 1

_≡_ : Nat -> Nat -> Set
n ≡ m = IsTrue (n == m)

{-# BUILTIN NATEQUALS _==_ #-}
{-# BUILTIN NATLESS   _<_  #-}

