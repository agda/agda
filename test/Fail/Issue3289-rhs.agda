open import Agda.Builtin.Nat

record R : Set where
  field
    x : Nat

open R {{...}}

f₁ : R

-- This is fine.
x ⦃ f₁ ⦄ = 0

-- THIS WORKS BUT MAKES NO SENSE!!!
_ : Nat
_ = f₁ {{ .x }}
