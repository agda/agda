
module Fin where

open import Prelude
open import Star
open import Position
open import Nat
open import Vec

Fin : Nat -> Set
Fin n = Pos (Step True) (n , low) (zero , high) 

fzero : {n : Nat} -> Fin (suc n)
fzero {n} = edge (step _) • map h next (vec _)
  where
    h : Nat -> Nat × Bit
    h x = (x , high)

fsuc : {n : Nat} -> Fin n -> Fin (suc n)
fsuc i = next (step _) • i

