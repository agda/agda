
module Nat where

import Bool
open Bool

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

infixr 25 _+_

_+_ : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)

infix 10 _==_ _<_

_==_ : Nat -> Nat -> Bool
zero  == zero  = true
suc n == zero  = false
zero  == suc m = false
suc n == suc m = n == m

_<_ : Nat -> Nat -> Bool
n     < zero  = false
zero  < suc m = true
suc n < suc m = n < m

