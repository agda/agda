------------------------------------------------------------------------
-- The Agda standard library
--
-- Instantiates the ring solver with two copies of the same ring with
-- decidable equality
------------------------------------------------------------------------

open import Algebra.RingSolver.AlmostCommutativeRing
open import Relation.Binary

module Algebra.RingSolver.Simple
         {r₁ r₂} (R : AlmostCommutativeRing r₁ r₂)
         (_≟_ : Decidable (AlmostCommutativeRing._≈_ R))
         where

open AlmostCommutativeRing R
import Algebra.RingSolver as RS
open RS rawRing R (-raw-almostCommutative⟶ R) _≟_ public
