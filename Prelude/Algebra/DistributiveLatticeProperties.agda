------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

open import Prelude.Algebraoid

module Prelude.Algebra.DistributiveLatticeProperties
  (dl : DistributiveLatticoid)
  where

open import Prelude.BinaryRelation
open import Prelude.Function
open import Prelude.Product
open Π
import Prelude.PreorderProof
import Prelude.Algebra
import Prelude.Algebra.LatticeProperties
private
  open module L = DistributiveLatticoid dl
  open module L = Prelude.Algebra setoid
  open module L = DistributiveLattice distLattice
  open module L = Lattice lattice
  open module S = Setoid setoid
  open module S = Equivalence equiv
  open module S = Prelude.PreorderProof (setoid⟶preSetoid setoid)

------------------------------------------------------------------------
-- A distributive lattice is a lattice

latticoid : Latticoid
latticoid = record
  { setoid  = setoid
  ; _∨_     = _∨_
  ; _∧_     = _∧_
  ; lattice = lattice
  }

private
  module LP = Prelude.Algebra.LatticeProperties latticoid
open LP public

------------------------------------------------------------------------
-- Some properties

abstract

  ∨-∧-distrib : _∨_ DistributesOver _∧_
  ∨-∧-distrib = ∨-∧-distribˡ , ∨-∧-distribʳ
    where
    ∨-∧-distribʳ : _∨_ DistributesOverʳ _∧_
    ∨-∧-distribʳ x y z =
      (y ∧ z) ∨ x
                         ≃⟨ ∨-comm _ _ ⟩
      x ∨ (y ∧ z)
                         ≃⟨ ∨-∧-distribˡ _ _ _ ⟩
      (x ∨ y) ∧ (x ∨ z)
                         ≃⟨ ∨-comm _ _ ⟨ ∧-pres-≈ ⟩ ∨-comm _ _ ⟩
      (y ∨ x) ∧ (z ∨ x)
                         ∎

  ∧-∨-distrib : _∧_ DistributesOver _∨_
  ∧-∨-distrib = ∧-∨-distribˡ , ∧-∨-distribʳ
    where
    ∧-∨-distribˡ : _∧_ DistributesOverˡ _∨_
    ∧-∨-distribˡ x y z =
      x ∧ (y ∨ z)
                                     ≃⟨ sym (proj₂ absorptive _ _) ⟨ ∧-pres-≈ ⟩ byDef ⟩
      (x ∧ (x ∨ y)) ∧ (y ∨ z)
                                     ≃⟨ (byDef ⟨ ∧-pres-≈ ⟩ ∨-comm _ _) ⟨ ∧-pres-≈ ⟩ byDef ⟩
      (x ∧ (y ∨ x)) ∧ (y ∨ z)
                                     ≃⟨ sym $ ∧-assoc _ _ _ ⟩
      x ∧ ((y ∨ x) ∧ (y ∨ z))
                                     ≃⟨ byDef ⟨ ∧-pres-≈ ⟩ sym (proj₁ ∨-∧-distrib _ _ _) ⟩
      x ∧ (y ∨ (x ∧ z))
                                     ≃⟨ sym (proj₁ absorptive _ _) ⟨ ∧-pres-≈ ⟩ byDef ⟩
      (x ∨ (x ∧ z)) ∧ (y ∨ (x ∧ z))
                                     ≃⟨ sym $ proj₂ ∨-∧-distrib _ _ _ ⟩
      (x ∧ y) ∨ (x ∧ z)
                        ∎

    ∧-∨-distribʳ : _∧_ DistributesOverʳ _∨_
    ∧-∨-distribʳ x y z =
      (y ∨ z) ∧ x
                         ≃⟨ ∧-comm _ _ ⟩
      x ∧ (y ∨ z)
                         ≃⟨ ∧-∨-distribˡ _ _ _ ⟩
      (x ∧ y) ∨ (x ∧ z)
                         ≃⟨ ∧-comm _ _ ⟨ ∨-pres-≈ ⟩ ∧-comm _ _ ⟩
      (y ∧ x) ∨ (z ∧ x)
                         ∎

  -- The dual construction is also a distributive lattice.

  ∧-∨-distLattice : DistributiveLattice _∧_ _∨_
  ∧-∨-distLattice = record
    { lattice      = ∧-∨-lattice
    ; ∨-∧-distribˡ = proj₁ ∧-∨-distrib
    }
