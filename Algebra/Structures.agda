------------------------------------------------------------------------
-- Some algebraic structures (not packed up with setoids and
-- operations)
------------------------------------------------------------------------

open import Relation.Binary

-- The structures are parameterised on an underlying equality.

module Algebra.Structures (s : Setoid) where

open Setoid s
import Algebra.FunctionProperties as P
open P s
import Relation.Binary.EqReasoning as EqR
open EqR s
open import Data.Function
open import Data.Product

private

  -- Some abbreviations:

  _Preserves-≈ : Op₁ -> Set
  • Preserves-≈ = • Preserves _≈_ → _≈_

  _Preserves₂-≈ : Op₂ -> Set
  • Preserves₂-≈ = • Preserves₂ _≈_ → _≈_ → _≈_

----------------------------------------------------------------------
-- One binary operation

record IsSemigroup (• : Op₂) : Set where
  field
    assoc    : Associative •
    •-pres-≈ : • Preserves₂-≈

record IsMonoid (• : Op₂) (ε : carrier) : Set where
  field
    isSemigroup : IsSemigroup •
    identity    : Identity ε •

  open IsSemigroup isSemigroup public

record IsCommutativeMonoid (• : Op₂) (ε : carrier) : Set where
  field
    isMonoid : IsMonoid • ε
    comm     : Commutative •

  open IsMonoid isMonoid public

record IsGroup (• : Op₂) (ε : carrier) (⁻¹ : Op₁) : Set where
  field
    isMonoid  : IsMonoid • ε
    inverse   : Inverse ε ⁻¹ •
    ⁻¹-pres-≈ : ⁻¹ Preserves-≈

  open IsMonoid isMonoid public

record IsAbelianGroup (• : Op₂) (ε : carrier) (⁻¹ : Op₁) : Set where
  field
    isGroup : IsGroup • ε ⁻¹
    comm    : Commutative •

  open IsGroup isGroup public

  isCommutativeMonoid : IsCommutativeMonoid • ε
  isCommutativeMonoid = record
    { isMonoid = isMonoid
    ; comm     = comm
    }

----------------------------------------------------------------------
-- Two binary operations

record IsSemiring (+ * : Op₂) (0# 1# : carrier) : Set where
  field
    +-isCommutativeMonoid : IsCommutativeMonoid + 0#
    *-isMonoid            : IsMonoid * 1#
    distrib               : * DistributesOver +
    zero                  : Zero 0# *

  open IsCommutativeMonoid +-isCommutativeMonoid public
         renaming ( assoc       to +-assoc
                  ; •-pres-≈    to +-pres-≈
                  ; isSemigroup to +-isSemigroup
                  ; identity    to +-identity
                  ; isMonoid    to +-isMonoid
                  ; comm        to +-comm
                  )

  open IsMonoid *-isMonoid public
         renaming ( assoc       to *-assoc
                  ; •-pres-≈    to *-pres-≈
                  ; isSemigroup to *-isSemigroup
                  ; identity    to *-identity
                  )

record IsCommutativeSemiring (+ * : Op₂) (0# 1# : carrier) : Set where
  field
    isSemiring : IsSemiring + * 0# 1#
    *-comm     : Commutative *

  open IsSemiring isSemiring public

  *-isCommutativeMonoid : IsCommutativeMonoid * 1#
  *-isCommutativeMonoid = record
      { isMonoid = *-isMonoid
      ; comm     = *-comm
      }

record IsRing (_+_ _*_ : Op₂) (-_ : Op₁) (0# 1# : carrier) : Set where
  field
    +-isAbelianGroup : IsAbelianGroup _+_ 0# -_
    *-isMonoid       : IsMonoid _*_ 1#
    distrib          : _*_ DistributesOver _+_

  open IsAbelianGroup +-isAbelianGroup public
         renaming ( assoc               to +-assoc
                  ; •-pres-≈            to +-pres-≈
                  ; isSemigroup         to +-isSemigroup
                  ; identity            to +-identity
                  ; isMonoid            to +-isMonoid
                  ; inverse             to --inverse
                  ; ⁻¹-pres-≈           to --pres-≈
                  ; isGroup             to +-isGroup
                  ; comm                to +-comm
                  ; isCommutativeMonoid to +-isCommutativeMonoid
                  )

  open IsMonoid *-isMonoid public
         renaming ( assoc       to *-assoc
                  ; •-pres-≈    to *-pres-≈
                  ; isSemigroup to *-isSemigroup
                  ; identity    to *-identity
                  )

  zero : Zero 0# _*_
  zero = (zeroˡ , zeroʳ)
    where
    zeroˡ : LeftZero 0# _*_
    zeroˡ x = begin
        0# * x                              ≈⟨ sym $ proj₂ +-identity _ ⟩
       (0# * x) +            0#             ≈⟨ byDef ⟨ +-pres-≈ ⟩ sym (proj₂ --inverse _) ⟩
       (0# * x) + ((0# * x)  + - (0# * x))  ≈⟨ +-assoc _ _ _ ⟩
      ((0# * x) +  (0# * x)) + - (0# * x)   ≈⟨ sym (proj₂ distrib _ _ _) ⟨ +-pres-≈ ⟩ byDef ⟩
             ((0# + 0#) * x) + - (0# * x)   ≈⟨ (proj₂ +-identity _ ⟨ *-pres-≈ ⟩ byDef)
                                                 ⟨ +-pres-≈ ⟩
                                               byDef ⟩
                    (0# * x) + - (0# * x)   ≈⟨ proj₂ --inverse _ ⟩
                             0#             ∎

    zeroʳ : RightZero 0# _*_
    zeroʳ x = begin
      x * 0#                              ≈⟨ sym $ proj₂ +-identity _ ⟩
      (x * 0#) + 0#                       ≈⟨ byDef ⟨ +-pres-≈ ⟩ sym (proj₂ --inverse _) ⟩
      (x * 0#) + ((x * 0#) + - (x * 0#))  ≈⟨ +-assoc _ _ _ ⟩
      ((x * 0#) + (x * 0#)) + - (x * 0#)  ≈⟨ sym (proj₁ distrib _ _ _) ⟨ +-pres-≈ ⟩ byDef ⟩
      (x * (0# + 0#)) + - (x * 0#)        ≈⟨ (byDef ⟨ *-pres-≈ ⟩ proj₂ +-identity _)
                                               ⟨ +-pres-≈ ⟩
                                             byDef ⟩
      (x * 0#) + - (x * 0#)               ≈⟨ proj₂ --inverse _ ⟩
      0#                                  ∎

  isSemiring : IsSemiring _+_ _*_ 0# 1#
  isSemiring = record
    { +-isCommutativeMonoid = +-isCommutativeMonoid
    ; *-isMonoid            = *-isMonoid
    ; distrib               = distrib
    ; zero                  = zero
    }

record IsCommutativeRing (+ * : Op₂) (- : Op₁) (0# 1# : carrier)
         : Set where
  field
    isRing : IsRing + * - 0# 1#
    *-comm : Commutative *

  open IsRing isRing public

  isCommutativeSemiring : IsCommutativeSemiring + * 0# 1#
  isCommutativeSemiring = record
    { isSemiring = isSemiring
    ; *-comm     = *-comm
    }

record IsLattice (∨ ∧ : Op₂) : Set where
  field
    ∨-comm     : Commutative ∨
    ∨-assoc    : Associative ∨
    ∨-pres-≈   : ∨ Preserves₂-≈
    ∧-comm     : Commutative ∧
    ∧-assoc    : Associative ∧
    ∧-pres-≈   : ∧ Preserves₂-≈
    absorptive : Absorptive ∨ ∧

record IsDistributiveLattice (∨ ∧ : Op₂) : Set where
  field
    isLattice    : IsLattice ∨ ∧
    ∨-∧-distribˡ : ∨ DistributesOverˡ ∧

  open IsLattice isLattice public

record IsBooleanAlgebra (∨ ∧ : Op₂) (¬ : Op₁) (⊤ ⊥ : carrier) : Set where
  field
    isDistributiveLattice : IsDistributiveLattice ∨ ∧
    ∨-complementʳ         : RightInverse ⊤ ¬ ∨
    ∧-complementʳ         : RightInverse ⊥ ¬ ∧
    ¬-pres-≈              : ¬ Preserves-≈

  open IsDistributiveLattice isDistributiveLattice public
