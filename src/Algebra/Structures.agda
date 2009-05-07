------------------------------------------------------------------------
-- Some algebraic structures (not packed up with sets, operations,
-- etc.)
------------------------------------------------------------------------

open import Relation.Binary

module Algebra.Structures where

import Algebra.FunctionProperties as FunctionProperties
open FunctionProperties using (Op₁; Op₂)
import Relation.Binary.EqReasoning as EqR
open import Data.Function
open import Data.Product

------------------------------------------------------------------------
-- One binary operation

record IsSemigroup {A} (≈ : Rel A) (∙ : Op₂ A) : Set where
  open FunctionProperties ≈
  field
    isEquivalence : IsEquivalence ≈
    assoc         : Associative ∙
    ∙-pres-≈      : ∙ Preserves₂ ≈ ⟶ ≈ ⟶ ≈

  open IsEquivalence isEquivalence public

record IsMonoid {A} (≈ : Rel A) (∙ : Op₂ A) (ε : A) : Set where
  open FunctionProperties ≈
  field
    isSemigroup : IsSemigroup ≈ ∙
    identity    : Identity ε ∙

  open IsSemigroup isSemigroup public

record IsCommutativeMonoid
         {A} (≈ : Rel A) (∙ : Op₂ A) (ε : A) : Set where
  open FunctionProperties ≈
  field
    isMonoid : IsMonoid ≈ ∙ ε
    comm     : Commutative ∙

  open IsMonoid isMonoid public

record IsGroup
         {A} (≈ : Rel A) (_∙_ : Op₂ A) (ε : A) (_⁻¹ : Op₁ A) : Set where
  open FunctionProperties ≈
  infixl 7 _-_
  field
    isMonoid  : IsMonoid ≈ _∙_ ε
    inverse   : Inverse ε _⁻¹ _∙_
    ⁻¹-pres-≈ : _⁻¹ Preserves ≈ ⟶ ≈

  open IsMonoid isMonoid public

  _-_ : Op₂ A
  x - y = x ∙ (y ⁻¹)

record IsAbelianGroup
         {A} (≈ : Rel A) (∙ : Op₂ A) (ε : A) (⁻¹ : Op₁ A) : Set where
  open FunctionProperties ≈
  field
    isGroup : IsGroup ≈ ∙ ε ⁻¹
    comm    : Commutative ∙

  open IsGroup isGroup public

  isCommutativeMonoid : IsCommutativeMonoid ≈ ∙ ε
  isCommutativeMonoid = record
    { isMonoid = isMonoid
    ; comm     = comm
    }

------------------------------------------------------------------------
-- Two binary operations

record IsNearSemiring {A} (≈ : Rel A) (+ * : Op₂ A) (0# : A) : Set where
  open FunctionProperties ≈
  field
    +-isMonoid    : IsMonoid ≈ + 0#
    *-isSemigroup : IsSemigroup ≈ *
    distribʳ      : * DistributesOverʳ +
    zeroˡ         : LeftZero 0# *

  open IsMonoid +-isMonoid public
         renaming ( assoc       to +-assoc
                  ; ∙-pres-≈    to +-pres-≈
                  ; isSemigroup to +-isSemigroup
                  ; identity    to +-identity
                  )

  open IsSemigroup *-isSemigroup public
         using ()
         renaming ( assoc    to *-assoc
                  ; ∙-pres-≈ to *-pres-≈
                  )

record IsSemiringWithoutOne
         {A} (≈ : Rel A) (+ * : Op₂ A) (0# : A) : Set where
  open FunctionProperties ≈
  field
    +-isCommutativeMonoid : IsCommutativeMonoid ≈ + 0#
    *-isSemigroup         : IsSemigroup ≈ *
    distrib               : * DistributesOver +
    zero                  : Zero 0# *

  open IsCommutativeMonoid +-isCommutativeMonoid public
         renaming ( assoc       to +-assoc
                  ; ∙-pres-≈    to +-pres-≈
                  ; isSemigroup to +-isSemigroup
                  ; identity    to +-identity
                  ; isMonoid    to +-isMonoid
                  ; comm        to +-comm
                  )

  open IsSemigroup *-isSemigroup public
         using ()
         renaming ( assoc       to *-assoc
                  ; ∙-pres-≈    to *-pres-≈
                  )

  isNearSemiring : IsNearSemiring ≈ + * 0#
  isNearSemiring = record
    { +-isMonoid    = +-isMonoid
    ; *-isSemigroup = *-isSemigroup
    ; distribʳ      = proj₂ distrib
    ; zeroˡ         = proj₁ zero
    }

record IsSemiringWithoutAnnihilatingZero
         {A} (≈ : Rel A) (+ * : Op₂ A) (0# 1# : A) : Set where
  open FunctionProperties ≈
  field
    -- Note that these structures do have an additive unit, but this
    -- unit does not necessarily annihilate multiplication.
    +-isCommutativeMonoid : IsCommutativeMonoid ≈ + 0#
    *-isMonoid            : IsMonoid ≈ * 1#
    distrib               : * DistributesOver +

  open IsCommutativeMonoid +-isCommutativeMonoid public
         renaming ( assoc       to +-assoc
                  ; ∙-pres-≈    to +-pres-≈
                  ; isSemigroup to +-isSemigroup
                  ; identity    to +-identity
                  ; isMonoid    to +-isMonoid
                  ; comm        to +-comm
                  )

  open IsMonoid *-isMonoid public
         using ()
         renaming ( assoc       to *-assoc
                  ; ∙-pres-≈    to *-pres-≈
                  ; isSemigroup to *-isSemigroup
                  ; identity    to *-identity
                  )

record IsSemiring {A} (≈ : Rel A) (+ * : Op₂ A) (0# 1# : A) : Set where
  open FunctionProperties ≈
  field
    isSemiringWithoutAnnihilatingZero :
      IsSemiringWithoutAnnihilatingZero ≈ + * 0# 1#
    zero : Zero 0# *

  open IsSemiringWithoutAnnihilatingZero
         isSemiringWithoutAnnihilatingZero public

  isSemiringWithoutOne : IsSemiringWithoutOne ≈ + * 0#
  isSemiringWithoutOne = record
    { +-isCommutativeMonoid = +-isCommutativeMonoid
    ; *-isSemigroup         = *-isSemigroup
    ; distrib               = distrib
    ; zero                  = zero
    }

  open IsSemiringWithoutOne isSemiringWithoutOne public
         using (isNearSemiring)

record IsCommutativeSemiringWithoutOne
         {A} (≈ : Rel A) (+ * : Op₂ A) (0# : A) : Set where
  open FunctionProperties ≈
  field
    isSemiringWithoutOne : IsSemiringWithoutOne ≈ + * 0#
    *-comm               : Commutative *

  open IsSemiringWithoutOne isSemiringWithoutOne public

record IsCommutativeSemiring
         {A} (≈ : Rel A) (+ * : Op₂ A) (0# 1# : A) : Set where
  open FunctionProperties ≈
  field
    isSemiring : IsSemiring ≈ + * 0# 1#
    *-comm     : Commutative *

  open IsSemiring isSemiring public

  *-isCommutativeMonoid : IsCommutativeMonoid ≈ * 1#
  *-isCommutativeMonoid = record
      { isMonoid = *-isMonoid
      ; comm     = *-comm
      }

  isCommutativeSemiringWithoutOne :
    IsCommutativeSemiringWithoutOne ≈ + * 0#
  isCommutativeSemiringWithoutOne = record
    { isSemiringWithoutOne = isSemiringWithoutOne
    ; *-comm               = *-comm
    }

record IsRing {A} (≈ : Rel A)
              (_+_ _*_ : Op₂ A) (-_ : Op₁ A) (0# 1# : A) : Set where
  open FunctionProperties ≈
  field
    +-isAbelianGroup : IsAbelianGroup ≈ _+_ 0# -_
    *-isMonoid       : IsMonoid ≈ _*_ 1#
    distrib          : _*_ DistributesOver _+_

  open IsAbelianGroup +-isAbelianGroup public
         renaming ( assoc               to +-assoc
                  ; ∙-pres-≈            to +-pres-≈
                  ; isSemigroup         to +-isSemigroup
                  ; identity            to +-identity
                  ; isMonoid            to +-isMonoid
                  ; inverse             to -‿inverse
                  ; ⁻¹-pres-≈           to -‿pres-≈
                  ; isGroup             to +-isGroup
                  ; comm                to +-comm
                  ; isCommutativeMonoid to +-isCommutativeMonoid
                  )

  open IsMonoid *-isMonoid public
         using ()
         renaming ( assoc       to *-assoc
                  ; ∙-pres-≈    to *-pres-≈
                  ; isSemigroup to *-isSemigroup
                  ; identity    to *-identity
                  )

  zero : Zero 0# _*_
  zero = (zeroˡ , zeroʳ)
    where
    open EqR (record { isEquivalence = isEquivalence })

    zeroˡ : LeftZero 0# _*_
    zeroˡ x = begin
        0# * x                              ≈⟨ sym $ proj₂ +-identity _ ⟩
       (0# * x) +            0#             ≈⟨ refl ⟨ +-pres-≈ ⟩ sym (proj₂ -‿inverse _) ⟩
       (0# * x) + ((0# * x)  + - (0# * x))  ≈⟨ sym $ +-assoc _ _ _ ⟩
      ((0# * x) +  (0# * x)) + - (0# * x)   ≈⟨ sym (proj₂ distrib _ _ _) ⟨ +-pres-≈ ⟩ refl ⟩
             ((0# + 0#) * x) + - (0# * x)   ≈⟨ (proj₂ +-identity _ ⟨ *-pres-≈ ⟩ refl)
                                                 ⟨ +-pres-≈ ⟩
                                               refl ⟩
                    (0# * x) + - (0# * x)   ≈⟨ proj₂ -‿inverse _ ⟩
                             0#             ∎

    zeroʳ : RightZero 0# _*_
    zeroʳ x = begin
      x * 0#                              ≈⟨ sym $ proj₂ +-identity _ ⟩
      (x * 0#) + 0#                       ≈⟨ refl ⟨ +-pres-≈ ⟩ sym (proj₂ -‿inverse _) ⟩
      (x * 0#) + ((x * 0#) + - (x * 0#))  ≈⟨ sym $ +-assoc _ _ _ ⟩
      ((x * 0#) + (x * 0#)) + - (x * 0#)  ≈⟨ sym (proj₁ distrib _ _ _) ⟨ +-pres-≈ ⟩ refl ⟩
      (x * (0# + 0#)) + - (x * 0#)        ≈⟨ (refl ⟨ *-pres-≈ ⟩ proj₂ +-identity _)
                                               ⟨ +-pres-≈ ⟩
                                             refl ⟩
      (x * 0#) + - (x * 0#)               ≈⟨ proj₂ -‿inverse _ ⟩
      0#                                  ∎

  isSemiringWithoutAnnihilatingZero
    : IsSemiringWithoutAnnihilatingZero ≈ _+_ _*_ 0# 1#
  isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = +-isCommutativeMonoid
    ; *-isMonoid            = *-isMonoid
    ; distrib               = distrib
    }

  isSemiring : IsSemiring ≈ _+_ _*_ 0# 1#
  isSemiring = record
    { isSemiringWithoutAnnihilatingZero =
        isSemiringWithoutAnnihilatingZero
    ; zero = zero
    }

  open IsSemiring isSemiring public
         using (isNearSemiring; isSemiringWithoutOne)

record IsCommutativeRing {A}
         (≈ : Rel A) (+ * : Op₂ A) (- : Op₁ A) (0# 1# : A) : Set where
  open FunctionProperties ≈
  field
    isRing : IsRing ≈ + * - 0# 1#
    *-comm : Commutative *

  open IsRing isRing public

  isCommutativeSemiring : IsCommutativeSemiring ≈ + * 0# 1#
  isCommutativeSemiring = record
    { isSemiring = isSemiring
    ; *-comm     = *-comm
    }

  open IsCommutativeSemiring isCommutativeSemiring public
         using (isCommutativeSemiringWithoutOne)

record IsLattice {A} (≈ : Rel A) (∨ ∧ : Op₂ A) : Set where
  open FunctionProperties ≈
  field
    isEquivalence : IsEquivalence ≈
    ∨-comm        : Commutative ∨
    ∨-assoc       : Associative ∨
    ∨-pres-≈      : ∨ Preserves₂ ≈ ⟶ ≈ ⟶ ≈
    ∧-comm        : Commutative ∧
    ∧-assoc       : Associative ∧
    ∧-pres-≈      : ∧ Preserves₂ ≈ ⟶ ≈ ⟶ ≈
    absorptive    : Absorptive ∨ ∧

  open IsEquivalence isEquivalence public

record IsDistributiveLattice {A} (≈ : Rel A) (∨ ∧ : Op₂ A) : Set where
  open FunctionProperties ≈
  field
    isLattice    : IsLattice ≈ ∨ ∧
    ∨-∧-distribʳ : ∨ DistributesOverʳ ∧

  open IsLattice isLattice public

record IsBooleanAlgebra
         {A} (≈ : Rel A) (∨ ∧ : Op₂ A) (¬ : Op₁ A) (⊤ ⊥ : A) : Set where
  open FunctionProperties ≈
  field
    isDistributiveLattice : IsDistributiveLattice ≈ ∨ ∧
    ∨-complementʳ         : RightInverse ⊤ ¬ ∨
    ∧-complementʳ         : RightInverse ⊥ ¬ ∧
    ¬-pres-≈              : ¬ Preserves ≈ ⟶ ≈

  open IsDistributiveLattice isDistributiveLattice public
