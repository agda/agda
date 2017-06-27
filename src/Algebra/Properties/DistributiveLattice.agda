------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

open import Algebra

module Algebra.Properties.DistributiveLattice
         {dl₁ dl₂} (DL : DistributiveLattice dl₁ dl₂)
         where

open DistributiveLattice DL
import Algebra.Properties.Lattice
private
  open module L = Algebra.Properties.Lattice lattice public
    hiding (replace-equality)
open import Algebra.Structures
open import Algebra.FunctionProperties _≈_
open import Relation.Binary
open import Relation.Binary.EqReasoning setoid
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; module Equivalence)
open import Data.Product

∨-∧-distribˡ : _∨_ DistributesOverˡ _∧_
∨-∧-distribˡ x y z = begin
  x ∨ y ∧ z          ≈⟨ ∨-comm _ _ ⟩
  y ∧ z ∨ x          ≈⟨ ∨-∧-distribʳ _ _ _ ⟩
  (y ∨ x) ∧ (z ∨ x)  ≈⟨ ∨-comm _ _ ⟨ ∧-cong ⟩ ∨-comm _ _ ⟩
  (x ∨ y) ∧ (x ∨ z)  ∎

∨-∧-distrib : _∨_ DistributesOver _∧_
∨-∧-distrib = ∨-∧-distribˡ , ∨-∧-distribʳ

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

∧-∨-distrib : _∧_ DistributesOver _∨_
∧-∨-distrib = ∧-∨-distribˡ , ∧-∨-distribʳ

-- The dual construction is also a distributive lattice.

∧-∨-isDistributiveLattice : IsDistributiveLattice _≈_ _∧_ _∨_
∧-∨-isDistributiveLattice = record
  { isLattice    = ∧-∨-isLattice
  ; ∨-∧-distribʳ = proj₂ ∧-∨-distrib
  }

∧-∨-distributiveLattice : DistributiveLattice _ _
∧-∨-distributiveLattice = record
  { _∧_                   = _∨_
  ; _∨_                   = _∧_
  ; isDistributiveLattice = ∧-∨-isDistributiveLattice
  }

-- One can replace the underlying equality with an equivalent one.

replace-equality :
  {_≈′_ : Rel Carrier dl₂} →
  (∀ {x y} → x ≈ y ⇔ (x ≈′ y)) → DistributiveLattice _ _
replace-equality {_≈′_} ≈⇔≈′ = record
  { _≈_                   = _≈′_
  ; _∧_                   = _∧_
  ; _∨_                   = _∨_
  ; isDistributiveLattice = record
    { isLattice    = Lattice.isLattice (L.replace-equality ≈⇔≈′)
    ; ∨-∧-distribʳ = λ x y z → to ⟨$⟩ ∨-∧-distribʳ x y z
    }
  } where open module E {x y} = Equivalence (≈⇔≈′ {x} {y})
