open import Agda.Builtin.Nat

record R : Set where
  field
    x : Nat

open R {{...}}

f₁ f₂ : R

-- This is fine.
x ⦃ f₁ ⦄ = 0

-- WAS: THIS WORKS BUT MAKES NO SENSE!!!
f₂ ⦃ .x ⦄ = 0

-- Error:

-- Cannot eliminate type R with pattern ⦃ .x ⦄ (suggestion: write .(x)
-- for a dot pattern, or remove the braces for a postfix projection)
-- when checking the clause left hand side
-- f₂ ⦃ .x ⦄
