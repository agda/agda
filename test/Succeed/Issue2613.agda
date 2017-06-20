-- Andreas, 2017-06-20, issue #2613, reported by Jonathan Prieto.
-- Regression introduced by fix of #2458 (which is obsolete since #2403)

module _ where

open import Agda.Builtin.Nat

module Prop (n : Nat) where

  data Prop : Set where
    _∧_ _∨_ : Prop → Prop → Prop

open Prop zero

data DView : Prop → Set where
  case₁ : (a b c : Prop) → DView ((a ∨ b) ∧ c)
  case₂ : (a : Prop)     → DView a

dView : (p : Prop) → DView p
dView ((a ∨ b) ∧ c) = case₁  _ _ _
dView a             = case₂ _

dist-∧ : Prop → Prop
dist-∧ p with dView p
dist-∧ .((a ∨ b) ∧ c) | case₁ a b c = dist-∧ (a ∧ c)
dist-∧ a              | case₂ .a = a

-- WAS:
-- Termination checking failed for the following functions:
--   dist-∧
-- Problematic calls:
--   dist-∧ (a ∧ c)

-- Should succeed.
