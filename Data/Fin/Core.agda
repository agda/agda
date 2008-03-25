------------------------------------------------------------------------
-- Finite sets (some core definitions)
------------------------------------------------------------------------

-- The definitions in this file are reexported by Data.Fin.

module Data.Fin.Core where

open import Data.Nat

------------------------------------------------------------------------
-- The type

data Fin : ℕ -> Set where
  fz : {n : ℕ} -> Fin (suc n)
  fs : {n : ℕ} -> Fin n -> Fin (suc n)

------------------------------------------------------------------------
-- Operations

-- raise m "n" = "m + n".

raise : forall {m} n -> Fin m -> Fin (n + m)
raise zero    i = i
raise (suc n) i = fs (raise n i)
