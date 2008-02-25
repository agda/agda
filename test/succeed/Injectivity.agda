
-- Simple test to check if constraint solving for injective
-- functions is working.
module Inj where

open import Lib.Nat
open import Lib.List

data U : Set where
  nat  : U
  list : U -> U

El : U -> Set
El nat      = Nat
El (list a) = List (El a)

sum : {a : U} -> El a -> Nat
sum {nat}    n  = n
sum {list a} xs = foldr _+_ 0 (map sum xs)

test₁ : Nat
test₁ = sum (1 :: [])

test₂ : Nat
test₂ = sum 1
