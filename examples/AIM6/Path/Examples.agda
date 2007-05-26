
module Examples where

open import Prelude
open import Star
open import Modal

List : Set -> Set
List A = Star (\_ _ -> A) tt tt

Nat = List True

zero : Nat
zero = ε

suc : Nat -> Nat
suc n = _ • n

-- Vectors

Vec : Set -> Nat -> Set
Vec A = All (\_ -> A)

-- Fin

Fin : Nat -> Set
Fin = Any (\_ -> True)
