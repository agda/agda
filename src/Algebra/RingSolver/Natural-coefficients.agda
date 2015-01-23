------------------------------------------------------------------------
-- The Agda standard library
--
-- Instantiates the ring solver, using the natural numbers as the
-- coefficient "ring"
------------------------------------------------------------------------

open import Algebra
import Algebra.Operations
open import Relation.Nullary

module Algebra.RingSolver.Natural-coefficients
         {r₁ r₂}
         (R : CommutativeSemiring r₁ r₂)
         (dec : let open CommutativeSemiring R
                    open Algebra.Operations semiring in
                ∀ m n → Dec (m × 1# ≈ n × 1#)) where

import Algebra.RingSolver
open import Algebra.RingSolver.AlmostCommutativeRing
open import Data.Nat.Base as ℕ
open import Data.Product using (module Σ)
open import Function
import Relation.Binary.EqReasoning
import Relation.Nullary.Decidable as Dec

open CommutativeSemiring R
open Algebra.Operations semiring
open Relation.Binary.EqReasoning setoid

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
  --
  -- Note that _×′_ is used rather than _×_. If _×_ were used, then
  -- Function.Related.TypeIsomorphisms.test would fail to type-check.

  homomorphism :
    ℕ-ring -Raw-AlmostCommutative⟶ fromCommutativeSemiring R
  homomorphism = record
    { ⟦_⟧    = λ n → n ×′ 1#
    ; +-homo = ×′-homo-+ 1#
    ; *-homo = ×′1-homo-*
    ; -‿homo = λ _ → refl
    ; 0-homo = refl
    ; 1-homo = refl
    }

  -- Equality of certain expressions can be decided.

  dec′ : ∀ m n → Dec (m ×′ 1# ≈ n ×′ 1#)
  dec′ m n = Dec.map′ to from (dec m n)
    where
    to : m × 1# ≈ n × 1# → m ×′ 1# ≈ n ×′ 1#
    to m≈n = begin
      m ×′ 1#  ≈⟨ sym $ ×≈×′ m 1# ⟩
      m ×  1#  ≈⟨ m≈n ⟩
      n ×  1#  ≈⟨ ×≈×′ n 1# ⟩
      n ×′ 1#  ∎

    from : m ×′ 1# ≈ n ×′ 1# → m × 1# ≈ n × 1#
    from m≈n = begin
      m ×  1#  ≈⟨ ×≈×′ m 1# ⟩
      m ×′ 1#  ≈⟨ m≈n ⟩
      n ×′ 1#  ≈⟨ sym $ ×≈×′ n 1# ⟩
      n ×  1#  ∎

-- The instantiation.

open Algebra.RingSolver _ _ homomorphism dec′ public
