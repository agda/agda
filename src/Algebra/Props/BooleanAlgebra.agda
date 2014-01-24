------------------------------------------------------------------------
-- The Agda standard library
--
-- Compatibility module. Pending for removal. Use
-- Algebra.Properties.BooleanAlgebra instead.
------------------------------------------------------------------------

open import Algebra

module Algebra.Props.BooleanAlgebra
         {b₁ b₂} (B : BooleanAlgebra b₁ b₂)
         where

open import Algebra.Properties.BooleanAlgebra B public
