open import Agda.Builtin.Nat

record R : Set where
  field
    r₁ : Nat
    r₂ : Nat
open R

h' : (n : Nat) → R
h' zero .r₁ = 1
h' zero .r₂ = 2
h' (suc n) = record { r₁ = n; r₂ = n }

-- Andreas, 2025-10-25, issue #8139
-- This case by Jesper (issue #2833, 2027-11-03) is now passing.
-- WAS: test/Fail/Issue2833.agda

h : (n : Nat) → R
h zero .r₁ = 1
h zero .r₂ = 2
h = λ n → record { r₁ = n; r₂ = n }
