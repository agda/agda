open import Agda.Builtin.Nat

record R : Set where
  field
    x : Nat

open R {{...}}

f₁ f₂ : R

-- This is fine.
x ⦃ f₁ ⦄ = 0

-- WAS: THIS WORKS BUT MAKES NO SENSE!!!
f₂ .⦃ x ⦄ = 0

-- error: [CannotEliminateWithPattern]
-- Cannot eliminate type R with dot pattern ⦃ .x ⦄ (did you supply too many arguments?)
-- when checking the clause left hand side
-- f₂ ⦃ .x ⦄
