module Prelude.Fin where

open import Prelude.Eq
open import Prelude.Nat

data Fin : Nat -> Set where
  fz : ∀{n} -> Fin (S n)
  fs : ∀{n} -> Fin n -> Fin (S n)

forget : {n : Nat} -> Fin n -> Nat
forget fz     = Z
forget (fs n) = S (forget n)

inject : (n : Nat) -> Fin (S n)
inject Z = fz
inject (S n) = fs (inject n)

inc : {n : Nat} -> Fin n -> Fin (S n)
inc fz     = fz
inc (fs n) = fs (inc n)