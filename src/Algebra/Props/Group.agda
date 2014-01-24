------------------------------------------------------------------------
-- The Agda standard library
--
-- Compatibility module. Pending for removal. Use
-- Algebra.Properties.Group instead.
------------------------------------------------------------------------

open import Algebra

module Algebra.Props.Group {g₁ g₂} (G : Group g₁ g₂) where

open import Algebra.Properties.Group G public
