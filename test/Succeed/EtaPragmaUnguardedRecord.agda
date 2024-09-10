-- Andreas, 2024-09-04
-- Unguarded records need ETA pragma rather than eta-equality directive.

-- {-# OPTIONS --safe #-}  -- Safe forbids ETA pragmas.

open import Agda.Builtin.Bool

data ⊥ : Set where

-- Guarding.
data Wrap (A : Set) : Set where
  wrap : A → Wrap A

-- Only T true is guarding, not T false.
T : Bool → Set → Set
T true = Wrap
T false A = A

-- R is not recognized as guarded record, so should not have eta.
record R : Set where
  inductive
  eta-equality         -- Should be ignored with a warning
  field
    tag : Bool
    possibly-unguarded : T tag R
    absurd : ⊥

-- Forcing eta for R.

{-# ETA R #-}
{-# ETA R #-}  -- Duplicate, thus useless, should trigger warning.

test : R → ⊥
test ()

-- Should succeed.
