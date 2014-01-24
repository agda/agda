------------------------------------------------------------------------
-- The Agda standard library
--
-- Compatibility module. Pending for removal. Use
-- Algebra.Properties.Ring instead.
------------------------------------------------------------------------

open import Algebra

module Algebra.Props.Ring {r₁ r₂} (R : Ring r₁ r₂) where

open import Algebra.Properties.Ring R public
