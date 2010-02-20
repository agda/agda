------------------------------------------------------------------------
-- Instantiates the ring solver with two copies of the same ring
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

open import Algebra.RingSolver.AlmostCommutativeRing

module Algebra.RingSolver.Simple
         {r₁ r₂} (R : AlmostCommutativeRing r₁ r₂)
         where

open AlmostCommutativeRing R
import Algebra.RingSolver as RS
open RS rawRing R (-raw-almostCommutative⟶ R) public
