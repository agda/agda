------------------------------------------------------------------------
-- The Agda standard library
--
-- Compatibility module. Pending for removal. Use
-- Algebra.Properties.Lattice instead.
------------------------------------------------------------------------

open import Algebra

module Algebra.Props.Lattice {l₁ l₂} (L : Lattice l₁ l₂) where

open import Algebra.Properties.Lattice L public
