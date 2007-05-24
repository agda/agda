
module Nat where

open import Prelude
open import Star

Nat : Set
Nat = Star One _ _

zero : Nat
zero = ε

suc : Nat -> Nat
suc n = _ • n

_+_ : Nat -> Nat -> Nat
_+_ = _++_

_*_ : Nat -> Nat -> Nat
x * y = bind id (\ _ -> y) x

test : Nat
test = suc (suc zero) * suc (suc zero)

