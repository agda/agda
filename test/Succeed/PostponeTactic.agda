-- Test that postponing tactic applications work properly

module _ where

open import Common.Prelude
open import Common.Reflection

data Zero : Set where
  zero : Zero

macro
  fill : Term → Tactic
  fill = give

_asTypeOf_ : {A : Set} → A → A → A
x asTypeOf _ = x

-- Requires postponing the macro evaluation until the 'zero' has been
-- disambiguated.
foo : Nat
foo = let z = zero in
      fill z asTypeOf z
