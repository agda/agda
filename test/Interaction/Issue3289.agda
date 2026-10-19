{-# OPTIONS --postfix-projections #-}

open import Agda.Builtin.Nat

record R : Set where
  field
    x : Nat → Nat

open R {{...}}

f : R
f .x = {!!}

-- WAS: Case splitting on result produces the following nonsense:
-- f ⦃ .x ⦄ x₁ = ?

-- SHOULD: produce
-- f .x x₁ = ?
