------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

open import Algebra

module Algebra.Props.Lattice {l₁ l₂} (L : Lattice l₁ l₂) where

open Lattice L
open import Algebra.Structures
import Algebra.FunctionProperties as P; open P _≈_
import Relation.Binary.EqReasoning as EqR; open EqR setoid
open import Function
open import Data.Product

∧-idempotent : Idempotent _∧_
∧-idempotent x = begin
  x ∧ x            ≈⟨ refl ⟨ ∧-cong ⟩ sym (proj₁ absorptive _ _) ⟩
  x ∧ (x ∨ x ∧ x)  ≈⟨ proj₂ absorptive _ _ ⟩
  x                ∎

∨-idempotent : Idempotent _∨_
∨-idempotent x = begin
  x ∨ x      ≈⟨ refl ⟨ ∨-cong ⟩ sym (∧-idempotent _) ⟩
  x ∨ x ∧ x  ≈⟨ proj₁ absorptive _ _ ⟩
  x          ∎

-- The dual construction is also a lattice.

∧-∨-isLattice : IsLattice _≈_ _∧_ _∨_
∧-∨-isLattice = record
  { isEquivalence = isEquivalence
  ; ∨-comm        = ∧-comm
  ; ∨-assoc       = ∧-assoc
  ; ∨-cong        = ∧-cong
  ; ∧-comm        = ∨-comm
  ; ∧-assoc       = ∨-assoc
  ; ∧-cong        = ∨-cong
  ; absorptive    = swap absorptive
  }

∧-∨-lattice : Lattice _ _
∧-∨-lattice = record
  { _∧_       = _∨_
  ; _∨_       = _∧_
  ; isLattice = ∧-∨-isLattice
  }
