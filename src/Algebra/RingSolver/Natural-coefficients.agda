------------------------------------------------------------------------
-- The Agda standard library
--
-- Instantiates the ring solver, using the natural numbers as the
-- coefficient "ring"
------------------------------------------------------------------------

open import Algebra

module Algebra.RingSolver.Natural-coefficients
         {r₁ r₂} (R : CommutativeSemiring r₁ r₂) where

import Algebra.Operations
import Algebra.RingSolver
open import Algebra.RingSolver.AlmostCommutativeRing
open import Data.Nat as ℕ
open import Data.Product using (module Σ)
open import Function

open CommutativeSemiring R
open Algebra.Operations semiring

private

  -- The coefficient "ring".

  ℕ-ring : RawRing _
  ℕ-ring = record
    { Carrier = ℕ
    ; _+_     = ℕ._+_
    ; _*_     = ℕ._*_
    ; -_      = id
    ; 0#      = 0
    ; 1#      = 1
    }

  -- There is a homomorphism from ℕ to R.

  homomorphism :
    ℕ-ring -Raw-AlmostCommutative⟶ fromCommutativeSemiring R
  homomorphism = record
    { ⟦_⟧    = λ n → n × 1#
    ; +-homo = ×-homo-+ 1#
    ; *-homo = ×1-homo-*
    ; -‿homo = λ _ → refl
    ; 0-homo = refl
    ; 1-homo = refl
    }

-- The instantiation.

open Algebra.RingSolver _ _ homomorphism public
