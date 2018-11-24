
open import Agda.Builtin.Nat

record R : Set where
  field
    r₁ : Nat
    r₂ : Nat
open R

h : (n : Nat) → R
r₁ (h zero) = {!!}
r₂ (h zero) = {!!}
h = {!!}
