------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

open import Algebra

module Algebra.Props.Lattice (l : Lattice) where

open Lattice l
import Algebra.Structures as S; open S setoid
import Algebra.FunctionProperties as P; open P setoid
import Relation.Binary.EqReasoning as EqR; open EqR setoid
open import Data.Function
open import Data.Product

∧-idempotent : Idempotent _∧_
∧-idempotent x = begin
  x ∧ x            ≈⟨ byDef ⟨ ∧-pres-≈ ⟩ sym (proj₁ absorptive _ _) ⟩
  x ∧ (x ∨ x ∧ x)  ≈⟨ proj₂ absorptive _ _ ⟩
  x                ∎

∨-idempotent : Idempotent _∨_
∨-idempotent x = begin
  x ∨ x      ≈⟨ byDef ⟨ ∨-pres-≈ ⟩ sym (∧-idempotent _) ⟩
  x ∨ x ∧ x  ≈⟨ proj₁ absorptive _ _ ⟩
  x          ∎

-- The dual construction is also a lattice.

∧-∨-isLattice : IsLattice _∧_ _∨_
∧-∨-isLattice = record
  { ∨-comm     = ∧-comm
  ; ∨-assoc    = ∧-assoc
  ; ∨-pres-≈   = ∧-pres-≈
  ; ∧-comm     = ∨-comm
  ; ∧-assoc    = ∨-assoc
  ; ∧-pres-≈   = ∨-pres-≈
  ; absorptive = swap absorptive
  }

∧-∨-lattice : Lattice
∧-∨-lattice = record
  { _∧_       = _∨_
  ; _∨_       = _∧_
  ; isLattice = ∧-∨-isLattice
  }
