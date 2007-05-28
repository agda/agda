
module Fin where

open import Prelude
open import Star
open import Modal
open import Nat

Fin : Nat -> Set
Fin = Any (\_ -> True)

fzero : {n : Nat} -> Fin (suc n)
fzero = done _ • ε

fsuc : {n : Nat} -> Fin n -> Fin (suc n)
fsuc i = step • i
