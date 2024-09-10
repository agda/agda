-- Andreas, 2024-09-04, example by Ulf
-- Unguarded eta records could make the type checker loop

{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Builtin.Equality

record R : Set where
  eta-equality         -- Should be ignored with a warning
  inductive
  field f : R

open R

loop : (let X = _) → X .f ≡ X .f → Set
loop refl = _

-- WAS: type checker loops

-- Should succeed with unsolved metas
