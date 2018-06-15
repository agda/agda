
open import Agda.Builtin.Nat

data Fin : Nat → Set where
  zero : {n : Nat}         → Fin (suc n)
  suc  : {n : Nat} → Fin n → Fin (suc n)

f : Fin 1 → Nat
f zero = 0
