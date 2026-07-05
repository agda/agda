{-# OPTIONS --cubical #-}

open import Agda.Builtin.Nat

variable
  n : Nat

data Fin : Nat → Set where
  zero : Fin (suc n)
  suc  : Fin n → Fin (suc n)

-- Simple with-on-Fin (indexed)
f : Fin 2 → Nat
f i with i
... | zero = 0
... | suc zero = 1

-- With-on-Fin with more branches
h : Fin 3 → Nat
h i with i
... | zero          = 0
... | suc zero      = 1
... | suc (suc zero) = 2
