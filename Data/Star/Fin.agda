------------------------------------------------------------------------
-- Finite sets defined in terms of Data.Star
------------------------------------------------------------------------

module Data.Star.Fin where

open import Data.Star
open import Data.Star.Nat
open import Data.Star.Decoration
open import Data.Unit

-- Finite sets are undecorated pointers into natural numbers.

Fin : ℕ -> Set
Fin = Any (\_ -> ⊤) (\_ -> ⊤)

-- "Constructors".

fz : forall {n} -> Fin (suc n)
fz = this tt

fs : forall {n} -> Fin n -> Fin (suc n)
fs = that tt
