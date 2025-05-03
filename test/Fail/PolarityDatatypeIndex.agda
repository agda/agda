-- Andreas, 2025-05-03
-- Specific error DatatypeIndexPolarity instead of GenericError.

{-# OPTIONS --polarity #-}

open import Agda.Builtin.Nat

FSort = @++ Nat → Set

data Fin : FSort where
  fzero : ∀{n} → Fin (suc n)
  fsuc  : ∀{n} → Fin n → Fin (suc n)

-- Expected error: [DatatypeIndexPolarity]
-- Cannot annotate datatype indices with polarity other than @mixed
