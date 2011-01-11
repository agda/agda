------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

open import Algebra

module Algebra.Props.Lattice {l₁ l₂} (L : Lattice l₁ l₂) where

open Lattice L
open import Algebra.Structures
import Algebra.FunctionProperties as P; open P _≈_
open import Relation.Binary
import Relation.Binary.EqReasoning as EqR; open EqR setoid
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence
  using (_⇔_; equivalent; module Equivalent) renaming (Equivalent to E)
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

poset : Poset _ _ _
poset = record
  { Carrier        = Carrier
  ; _≈_            = _≈_
  ; _≤_            = _≤_
  ; isPartialOrder = record 
    { isPreorder = record 
      { isEquivalence = isEquivalence
      ; reflexive = λ i≈j → sym (trans (∧-cong refl (sym i≈j)) (∧-idempotent _))
      ; trans = λ {i} {j} {k} i≈i∧j j≈j∧k → begin
        i           ≈⟨ i≈i∧j ⟩
        i ∧ j       ≈⟨ ∧-cong refl j≈j∧k ⟩
        i ∧ (j ∧ k) ≈⟨ (sym (∧-assoc _ _ _)) ⟩
        (i ∧ j) ∧ k ≈⟨ ∧-cong (sym i≈i∧j) refl ⟩
        i ∧ k       ∎
      }
  ; antisym = λ x≈x∧y y≈y∧x → trans (trans x≈x∧y (∧-comm _ _)) (sym y≈y∧x) }
  }

≈⇔≈‵-isLattice : {_≈‵_ : Rel Carrier l₂} → (∀ {x y} → x ≈ y ⇔ x ≈‵ y) → IsLattice _≈‵_ _∨_ _∧_
≈⇔≈‵-isLattice ≈⇔≈‵ = record
  { isEquivalence = record 
    { refl = (E.to ≈⇔≈‵) ⟨$⟩ refl
    ; sym = λ x≈y → E.to ≈⇔≈‵ ⟨$⟩ sym (E.from ≈⇔≈‵ ⟨$⟩ x≈y)
    ; trans = λ x≈y y≈z → (E.to ≈⇔≈‵) ⟨$⟩ trans ((E.from ≈⇔≈‵) ⟨$⟩ x≈y) ((E.from ≈⇔≈‵) ⟨$⟩ y≈z)  
    }
  ; ∨-comm = λ x y → E.to ≈⇔≈‵ ⟨$⟩ (∨-comm x y)
  ; ∨-assoc = λ x y z → E.to ≈⇔≈‵ ⟨$⟩ (∨-assoc x y z)
  ; ∨-cong = λ x≈‵y u≈‵v → E.to ≈⇔≈‵ ⟨$⟩ ∨-cong (E.from ≈⇔≈‵ ⟨$⟩ x≈‵y) (E.from ≈⇔≈‵ ⟨$⟩ u≈‵v)
  ; ∧-comm = λ x y → E.to ≈⇔≈‵ ⟨$⟩ ∧-comm x y
  ; ∧-assoc = λ x y z → E.to ≈⇔≈‵ ⟨$⟩ ∧-assoc x y z
  ; ∧-cong = λ x≈‵y u≈‵v → E.to ≈⇔≈‵ ⟨$⟩ ∧-cong (E.from ≈⇔≈‵ ⟨$⟩ x≈‵y) (E.from ≈⇔≈‵ ⟨$⟩ u≈‵v)
  ; absorptive = (λ x y → (Equivalent.to ≈⇔≈‵) ⟨$⟩ (proj₁ absorptive) x y)
               , (λ x y → (Equivalent.to ≈⇔≈‵) ⟨$⟩ (proj₂ absorptive) x y) 
  }

≈⇔≈‵-lattice : {_≈‵_ : Rel Carrier l₂} → (∀ {x y} → x ≈ y ⇔ x ≈‵ y) → Lattice _ _
≈⇔≈‵-lattice ≈⇔≈‵ = record 
  { _∧_ = _∧_
  ; _∨_ = _∨_
  ; isLattice = ≈⇔≈‵-isLattice ≈⇔≈‵
  }

