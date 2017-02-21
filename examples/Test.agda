module Agda.Test where

open import Agda.Builtin.Nat
open import Agda.Builtin.Int
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Strict

foo : Nat -> Bool
foo zero = true
foo (suc _) = false

_-NZ_ : Nat → Nat → Int
a -NZ b with a < b
... | true  = negsuc (b - suc a)
... | false = pos (a - b)
{-# INLINE _-NZ_ #-}

_+Z_ : Int → Int → Int
pos    a +Z pos    b = pos (a + b)
pos    a +Z negsuc b = a -NZ suc b
negsuc a +Z pos    b = b -NZ suc a
negsuc a +Z negsuc b = negsuc (suc a + b)
{-# INLINE _+Z_ #-}


sum : List Int → Int
sum []       = pos 0
sum (x ∷ xs) = x +Z sum xs

sum' : List Int → Int → Int
sum' [] n = n
sum' (x ∷ xs) n = primForce (n +Z x) λ n' → sum' xs n'
