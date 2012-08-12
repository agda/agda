------------------------------------------------------------------------
-- The Agda standard library
--
-- Instantiates the ring solver with two copies of the same ring
-- The ring must have decidable equality
------------------------------------------------------------------------

open import Algebra.RingSolver.AlmostCommutativeRing
open import Relation.Binary.Core

module Algebra.RingSolver.Simple
         {r₁ r₂} (R : AlmostCommutativeRing r₁ r₂)
         (_≟_ : Decidable (AlmostCommutativeRing._≈_ R))
         where

open AlmostCommutativeRing R
import Algebra.RingSolver as RS
open RS rawRing R (-raw-almostCommutative⟶ R) (_≟_) public
