{-# OPTIONS --cubical #-}

open import Agda.Builtin.Nat

variable
  n : Nat

data Fin : Nat → Set where
  zero : Fin (suc n)
  suc  : Fin n → Fin (suc n)

-- Incomplete pattern on an INDEXED type.
-- This forces the coverage checker to generate a transpX clause
-- using tau/leftInv from our injectivity retract.
f : Fin 2 → Nat
f zero = 0
-- Missing: suc zero case
