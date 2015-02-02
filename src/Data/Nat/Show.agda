------------------------------------------------------------------------
-- The Agda standard library
--
-- Showing natural numbers
------------------------------------------------------------------------

module Data.Nat.Show where

open import Data.Nat
open import Relation.Nullary.Decidable using (True)
open import Data.String.Base as String using (String)
open import Data.Digit
open import Data.Product using (proj₁)
open import Function
open import Data.List.Base

-- showInBase b n is a string containing the representation of n in
-- base b.

showInBase : (base : ℕ)
             {base≥2 : True (2 ≤? base)}
             {base≤16 : True (base ≤? 16)} →
             ℕ → String
showInBase base {base≥2} {base≤16} n =
  String.fromList $
  map (showDigit {base≤16 = base≤16}) $
  reverse $
  proj₁ $ toDigits base {base≥2 = base≥2} n

-- show n is a string containing the decimal expansion of n (starting
-- with the most significant digit).

show : ℕ → String
show = showInBase 10
