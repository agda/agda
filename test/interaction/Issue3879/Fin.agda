module Issue3879.Fin where

open import Agda.Builtin.Nat

data Fin : Nat → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)

pattern 0F = zero
