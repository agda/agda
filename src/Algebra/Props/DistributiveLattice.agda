------------------------------------------------------------------------
-- The Agda standard library
--
-- Compatibility module. Pending for removal. Use
-- Algebra.Properties.DistributiveLattice instead.
------------------------------------------------------------------------

open import Algebra

module Algebra.Props.DistributiveLattice
         {dl₁ dl₂} (DL : DistributiveLattice dl₁ dl₂)
         where

open import Algebra.Properties.DistributiveLattice DL public
