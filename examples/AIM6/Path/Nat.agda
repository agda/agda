
module Nat where

open import Prelude
open import Star

Nat : Set
Nat = Star One _ _

zero : Nat
zero = ε

suc : Nat -> Nat
suc n = _ • n

infixl 50 _+_ _-_
infixl 60 _*_

_+_ : Nat -> Nat -> Nat
_+_ = _++_

_*_ : Nat -> Nat -> Nat
x * y = bind id (\ _ -> y) x

_-_ : Nat -> Nat -> Nat
n       - ε       = n
ε       - m       = ε
(_ • n) - (_ • m) = n - m

test : Nat
test = suc (suc zero) * suc (suc zero)
