------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

open import Algebra

module Algebra.Props.DistributiveLattice
         (dl : DistributiveLattice)
         where

open DistributiveLattice dl
import Algebra.Props.Lattice as L; open L lattice public
open import Algebra.Structures
import Algebra.FunctionProperties as P; open P _≈_
import Relation.Binary.EqReasoning as EqR; open EqR setoid
open import Function
open import Data.Product

∨-∧-distrib : _∨_ DistributesOver _∧_
∨-∧-distrib = ∨-∧-distribˡ , ∨-∧-distribʳ
  where
  ∨-∧-distribˡ : _∨_ DistributesOverˡ _∧_
  ∨-∧-distribˡ x y z = begin
    x ∨ y ∧ z          ≈⟨ ∨-comm _ _ ⟩
    y ∧ z ∨ x          ≈⟨ ∨-∧-distribʳ _ _ _ ⟩
    (y ∨ x) ∧ (z ∨ x)  ≈⟨ ∨-comm _ _ ⟨ ∧-cong ⟩ ∨-comm _ _ ⟩
    (x ∨ y) ∧ (x ∨ z)  ∎

∧-∨-distrib : _∧_ DistributesOver _∨_
∧-∨-distrib = ∧-∨-distribˡ , ∧-∨-distribʳ
  where
  ∧-∨-distribˡ : _∧_ DistributesOverˡ _∨_
  ∧-∨-distribˡ x y z = begin
    x ∧ (y ∨ z)                ≈⟨ sym (proj₂ absorptive _ _) ⟨ ∧-cong ⟩ refl ⟩
    (x ∧ (x ∨ y)) ∧ (y ∨ z)    ≈⟨ (refl ⟨ ∧-cong ⟩ ∨-comm _ _) ⟨ ∧-cong ⟩ refl ⟩
    (x ∧ (y ∨ x)) ∧ (y ∨ z)    ≈⟨ ∧-assoc _ _ _ ⟩
    x ∧ ((y ∨ x) ∧ (y ∨ z))    ≈⟨ refl ⟨ ∧-cong ⟩ sym (proj₁ ∨-∧-distrib _ _ _) ⟩
    x ∧ (y ∨ x ∧ z)            ≈⟨ sym (proj₁ absorptive _ _) ⟨ ∧-cong ⟩ refl ⟩
    (x ∨ x ∧ z) ∧ (y ∨ x ∧ z)  ≈⟨ sym $ proj₂ ∨-∧-distrib _ _ _ ⟩
    x ∧ y ∨ x ∧ z              ∎

  ∧-∨-distribʳ : _∧_ DistributesOverʳ _∨_
  ∧-∨-distribʳ x y z = begin
    (y ∨ z) ∧ x    ≈⟨ ∧-comm _ _ ⟩
    x ∧ (y ∨ z)    ≈⟨ ∧-∨-distribˡ _ _ _ ⟩
    x ∧ y ∨ x ∧ z  ≈⟨ ∧-comm _ _ ⟨ ∨-cong ⟩ ∧-comm _ _ ⟩
    y ∧ x ∨ z ∧ x  ∎

-- The dual construction is also a distributive lattice.

∧-∨-isDistributiveLattice : IsDistributiveLattice _≈_ _∧_ _∨_
∧-∨-isDistributiveLattice = record
  { isLattice    = ∧-∨-isLattice
  ; ∨-∧-distribʳ = proj₂ ∧-∨-distrib
  }

∧-∨-distributiveLattice : DistributiveLattice
∧-∨-distributiveLattice = record
  { _∧_                   = _∨_
  ; _∨_                   = _∧_
  ; isDistributiveLattice = ∧-∨-isDistributiveLattice
  }
