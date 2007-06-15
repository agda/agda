open import Prelude.Algebraoid

module Prelude.Algebra.Operations (s : Semiringoid) where

open import Prelude.BinaryRelation
open import Prelude.Nat using (zero; suc; ℕ)
private
  open module R = Semiringoid s
  open module S = Setoid setoid

-- Multiplication by natural number.

_×_ : ℕ -> carrier -> carrier
zero  × x = 0#
suc n × x = x + (n × x)

-- Exponentiation.

_^_ : carrier -> ℕ -> carrier
x ^ zero  = 1#
x ^ suc n = x * (x ^ n)
