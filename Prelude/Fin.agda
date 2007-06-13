------------------------------------------------------------------------
-- Finite sets
------------------------------------------------------------------------

module Prelude.Fin where

open import Prelude.Nat

data Fin : ℕ -> Set where
  fz : {n : ℕ} -> Fin (suc n)
  fs : {n : ℕ} -> Fin n -> Fin (suc n)
