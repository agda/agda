------------------------------------------------------------------------
-- The Agda standard library
--
-- Universe levels
------------------------------------------------------------------------

module Level where

-- Levels.

open import Agda.Primitive public
  using    (Level; _⊔_)
  renaming (lzero to zero; lsuc to suc)

-- Lifting.

record Lift {a ℓ} (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field lower : A

open Lift public
