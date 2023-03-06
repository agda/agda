{-# OPTIONS --cubical-compatible --level-universe #-}
------------------------------------------------------------------------
-- Universe levels
------------------------------------------------------------------------

module Common.Level where

open import Agda.Primitive public using (LevelUniv; Level; lzero; lsuc; _⊔_)

-- Lifting.

record Lift {a ℓ} (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field lower : A

open Lift public
