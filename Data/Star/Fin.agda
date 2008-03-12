------------------------------------------------------------------------
-- Finite sets defined in terms of Data.Star
------------------------------------------------------------------------

module Data.Star.Fin where

open import Data.Star
open import Data.Star.Nat
open import Data.Star.Lookup

-- Finite sets.

Fin : ℕ -> Set
Fin = NonEmptyPrefixOf

-- "Constructors".

fz : forall {n} -> Fin (suc n)
fz = this

fs : forall {n} -> Fin n -> Fin (suc n)
fs = that
