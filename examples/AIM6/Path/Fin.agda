
module Fin where

open import Prelude
open import Star
open import Elem
open import Nat
open import Vec

Fin : Nat -> Set
Fin n = Elem (Step True) n zero 

fzero : {n : Nat} -> Fin (suc n)
fzero = (up , step _) • map (_,_ true) (_,_ ref) (vec _)

fsuc : {n : Nat} -> Fin n -> Fin (suc n)
fsuc i = (_ , step _) • i

