------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

open import Algebra

module Algebra.Properties.Lattice {l₁ l₂} (L : Lattice l₁ l₂) where

open Lattice L
open import Algebra.Structures
import Algebra.FunctionProperties as P; open P _≈_
open import Relation.Binary
import Relation.Binary.Lattice as R
import Relation.Binary.EqReasoning as EqR; open EqR setoid
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; module Equivalence)
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

-- Every lattice can be turned into a poset.

poset : Poset _ _ _
poset = record
  { Carrier        = Carrier
  ; _≈_            = _≈_
  ; _≤_            = λ x y → x ≈ x ∧ y
  ; isPartialOrder = record
    { isPreorder = record
      { isEquivalence = isEquivalence
      ; reflexive     = λ {i} {j} i≈j → begin
                          i      ≈⟨ sym $ ∧-idempotent _ ⟩
                          i ∧ i  ≈⟨ ∧-cong refl i≈j ⟩
                          i ∧ j  ∎
      ; trans         = λ {i} {j} {k} i≈i∧j j≈j∧k → begin
                          i            ≈⟨ i≈i∧j ⟩
                          i ∧ j        ≈⟨ ∧-cong refl j≈j∧k ⟩
                          i ∧ (j ∧ k)  ≈⟨ sym (∧-assoc _ _ _) ⟩
                          (i ∧ j) ∧ k  ≈⟨ ∧-cong (sym i≈i∧j) refl ⟩
                          i ∧ k        ∎
      }
    ; antisym = λ {x} {y} x≈x∧y y≈y∧x → begin
                  x      ≈⟨ x≈x∧y ⟩
                  x ∧ y  ≈⟨ ∧-comm _ _ ⟩
                  y ∧ x  ≈⟨ sym y≈y∧x ⟩
                  y      ∎
    }
  }

open Poset poset using (_≤_; isPartialOrder)

-- Every algebraic lattice can be turned into an order-theoretic one.

isOrderTheoreticLattice : R.IsLattice _≈_ _≤_ _∨_ _∧_
isOrderTheoreticLattice = record
  { isPartialOrder = isPartialOrder
  ; supremum       = λ x y →
                       sym (∧-absorbs-∨ x y) ,
                       (begin
                         y            ≈⟨ sym (∧-absorbs-∨ y x) ⟩
                         y ∧ (y ∨ x)  ≈⟨ ∧-cong refl (∨-comm y x) ⟩
                         y ∧ (x ∨ y)  ∎) ,
                       (λ z x≤z y≤z → sound (begin
                         (x ∨ y) ∨ z  ≈⟨ ∨-assoc x y z ⟩
                         x ∨ (y ∨ z)  ≈⟨ ∨-cong refl (complete y≤z) ⟩
                         x ∨ z        ≈⟨ complete x≤z  ⟩
                         z            ∎))
  ; infimum        = λ x y →
                       (begin
                         x ∧ y        ≈⟨ ∧-cong (sym (∧-idempotent x)) refl ⟩
                         (x ∧ x) ∧ y  ≈⟨ ∧-assoc x x y  ⟩
                         x ∧ (x ∧ y)  ≈⟨ ∧-comm x (x ∧ y) ⟩
                         (x ∧ y) ∧ x  ∎) ,
                       (begin
                         x ∧ y        ≈⟨ ∧-cong refl (sym (∧-idempotent y)) ⟩
                         x ∧ (y ∧ y)  ≈⟨ sym (∧-assoc x y y) ⟩
                         (x ∧ y) ∧ y  ∎) ,
                       (λ z z≈z∧x z≈z∧y → begin
                         z            ≈⟨ z≈z∧y ⟩
                         z ∧ y        ≈⟨ ∧-cong z≈z∧x refl ⟩
                         (z ∧ x) ∧ y  ≈⟨ ∧-assoc z x y ⟩
                         z ∧ (x ∧ y)  ∎)
  }
  where
    ∧-absorbs-∨ = proj₂ absorptive

    -- An alternative but equivalent interpretation of the order _≤_.

    complete : ∀ {x y} → x ≤ y → x ∨ y ≈ y
    complete {x} {y} x≈x∧y = begin
      x ∨ y        ≈⟨ ∨-cong x≈x∧y refl ⟩
      (x ∧ y) ∨ y  ≈⟨ ∨-cong (∧-comm x y) refl ⟩
      (y ∧ x) ∨ y  ≈⟨ ∨-comm (y ∧ x) y ⟩
      y ∨ (y ∧ x)  ≈⟨ proj₁ absorptive y x ⟩
      y            ∎

    sound : ∀ {x y} → x ∨ y ≈ y → x ≤ y
    sound {x} {y} x∨y≈y = begin
      x            ≈⟨ sym (∧-absorbs-∨ x y) ⟩
      x ∧ (x ∨ y)  ≈⟨ ∧-cong refl x∨y≈y ⟩
      x ∧ y        ∎

orderTheoreticLattice : R.Lattice _ _ _
orderTheoreticLattice = record { isLattice = isOrderTheoreticLattice }

-- One can replace the underlying equality with an equivalent one.

replace-equality : {_≈′_ : Rel Carrier l₂} →
                   (∀ {x y} → x ≈ y ⇔ (x ≈′ y)) → Lattice _ _
replace-equality {_≈′_} ≈⇔≈′ = record
  { _≈_       = _≈′_
  ; _∧_       = _∧_
  ; _∨_       = _∨_
  ; isLattice = record
    { isEquivalence = record
      { refl  = to ⟨$⟩ refl
      ; sym   = λ x≈y → to ⟨$⟩ sym (from ⟨$⟩ x≈y)
      ; trans = λ x≈y y≈z → to ⟨$⟩ trans (from ⟨$⟩ x≈y) (from ⟨$⟩ y≈z)
      }
    ; ∨-comm     = λ x y → to ⟨$⟩ ∨-comm x y
    ; ∨-assoc    = λ x y z → to ⟨$⟩ ∨-assoc x y z
    ; ∨-cong     = λ x≈y u≈v → to ⟨$⟩ ∨-cong (from ⟨$⟩ x≈y) (from ⟨$⟩ u≈v)
    ; ∧-comm     = λ x y → to ⟨$⟩ ∧-comm x y
    ; ∧-assoc    = λ x y z → to ⟨$⟩ ∧-assoc x y z
    ; ∧-cong     = λ x≈y u≈v → to ⟨$⟩ ∧-cong (from ⟨$⟩ x≈y) (from ⟨$⟩ u≈v)
    ; absorptive = (λ x y → to ⟨$⟩ proj₁ absorptive x y)
                 , (λ x y → to ⟨$⟩ proj₂ absorptive x y)
    }
  } where open module E {x y} = Equivalence (≈⇔≈′ {x} {y})
