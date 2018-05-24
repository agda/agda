{-# OPTIONS --no-print-pattern-synonyms #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

data Fin : Nat → Set where
  fzero : ∀ {n} → Fin (suc n)
  fsuc  : ∀ {n} → Fin n → Fin (suc n)

pattern #1 = fsuc fzero

prf : (i : Fin 2) → i ≡ #1
prf i = refl  -- should say i != fsuc fzero
