------------------------------------------------------------------------
-- The Agda standard library
--
-- Compatibility module. Pending for removal. Use
-- Algebra.Properties.AbelianGroup instead.
------------------------------------------------------------------------

open import Algebra

module Algebra.Props.AbelianGroup
         {g₁ g₂} (G : AbelianGroup g₁ g₂) where

open import Algebra.Properties.AbelianGroup G public
