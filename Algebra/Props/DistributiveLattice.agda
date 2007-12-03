------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

open import Algebra.Packaged

module Algebra.Props.DistributiveLattice
  (dl : DistributiveLatticoid)
  where

open import Relation.Binary
open import Data.Function
open import Data.Product
import Relation.Binary.EqReasoning
import Algebra
import Algebra.Props.Lattice
open DistributiveLatticoid dl
open Algebra setoid
open DistributiveLattice distLattice
open Lattice lattice
open SetoidOps setoid
open Relation.Binary.EqReasoning preorder

------------------------------------------------------------------------
-- A distributive lattice is a lattice

latticoid : Latticoid
latticoid = record
  { setoid  = setoid
  ; _∨_     = _∨_
  ; _∧_     = _∧_
  ; lattice = lattice
  }

open Algebra.Props.Lattice latticoid public

------------------------------------------------------------------------
-- Some properties

abstract

  ∨-∧-distrib : _∨_ DistributesOver _∧_
  ∨-∧-distrib = ∨-∧-distribˡ , ∨-∧-distribʳ
    where
    ∨-∧-distribʳ : _∨_ DistributesOverʳ _∧_
    ∨-∧-distribʳ x y z =
                         begin
      (y ∧ z) ∨ x
                         ∼⟨ ∨-comm _ _ ⟩
      x ∨ (y ∧ z)
                         ∼⟨ ∨-∧-distribˡ _ _ _ ⟩
      (x ∨ y) ∧ (x ∨ z)
                         ∼⟨ ∨-comm _ _ ⟨ ∧-pres-≈ ⟩ ∨-comm _ _ ⟩
      (y ∨ x) ∧ (z ∨ x)
                         ∎

  ∧-∨-distrib : _∧_ DistributesOver _∨_
  ∧-∨-distrib = ∧-∨-distribˡ , ∧-∨-distribʳ
    where
    ∧-∨-distribˡ : _∧_ DistributesOverˡ _∨_
    ∧-∨-distribˡ x y z =
                                     begin
      x ∧ (y ∨ z)
                                     ∼⟨ sym (proj₂ absorptive _ _) ⟨ ∧-pres-≈ ⟩ byDef ⟩
      (x ∧ (x ∨ y)) ∧ (y ∨ z)
                                     ∼⟨ (byDef ⟨ ∧-pres-≈ ⟩ ∨-comm _ _) ⟨ ∧-pres-≈ ⟩ byDef ⟩
      (x ∧ (y ∨ x)) ∧ (y ∨ z)
                                     ∼⟨ sym $ ∧-assoc _ _ _ ⟩
      x ∧ ((y ∨ x) ∧ (y ∨ z))
                                     ∼⟨ byDef ⟨ ∧-pres-≈ ⟩ sym (proj₁ ∨-∧-distrib _ _ _) ⟩
      x ∧ (y ∨ (x ∧ z))
                                     ∼⟨ sym (proj₁ absorptive _ _) ⟨ ∧-pres-≈ ⟩ byDef ⟩
      (x ∨ (x ∧ z)) ∧ (y ∨ (x ∧ z))
                                     ∼⟨ sym $ proj₂ ∨-∧-distrib _ _ _ ⟩
      (x ∧ y) ∨ (x ∧ z)
                        ∎

    ∧-∨-distribʳ : _∧_ DistributesOverʳ _∨_
    ∧-∨-distribʳ x y z =
                         begin
      (y ∨ z) ∧ x
                         ∼⟨ ∧-comm _ _ ⟩
      x ∧ (y ∨ z)
                         ∼⟨ ∧-∨-distribˡ _ _ _ ⟩
      (x ∧ y) ∨ (x ∧ z)
                         ∼⟨ ∧-comm _ _ ⟨ ∨-pres-≈ ⟩ ∧-comm _ _ ⟩
      (y ∧ x) ∨ (z ∧ x)
                         ∎

  -- The dual construction is also a distributive lattice.

  ∧-∨-distLattice : DistributiveLattice _∧_ _∨_
  ∧-∨-distLattice = record
    { lattice      = ∧-∨-lattice
    ; ∨-∧-distribˡ = proj₁ ∧-∨-distrib
    }
