
module Data.Nat where

import Data.Bool as Bool

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

module Arithmetic where

  infixl 60 _+_
  infixl 70 _*_

  _+_ : Nat -> Nat -> Nat
  zero  + m = m
  suc n + m = suc (n + m)

  _*_ : Nat -> Nat -> Nat
  zero  * m = zero
  suc n * m = n * m + m

module Equality where

  open Bool

  _==_ : Nat -> Nat -> Bool
  zero	== zero  = true
  zero	== suc _ = false
  suc _ == zero  = false
  suc n == suc m = n == m

  _≡_ : Nat -> Nat -> Set
  n ≡ m = IsTrue (n == m)

