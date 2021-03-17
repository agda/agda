open import Agda.Builtin.Nat

record R : Set where
  field
    x : Nat

open R {{...}}

f₁ : R

-- This is fine.
x ⦃ f₁ ⦄ = 0

-- WAS: THIS WORKS BUT MAKES NO SENSE!!!
_ : Nat
_ = f₁ {{ .x }}

-- Should raise an error.

-- Illegal hiding in postfix projection  ⦃ .x ⦄
-- when scope checking f₁ ⦃ .x ⦄
