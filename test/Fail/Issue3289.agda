open import Agda.Builtin.Nat

record R : Set where
  field
    x : Nat

open R {{...}}

f₁ f₂ : R

-- This is fine.
x ⦃ f₁ ⦄ = 0

-- THIS WORKS BUT MAKES NO SENSE!!!
f₂ ⦃ .x ⦄ = 0
