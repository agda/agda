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

record IsGroup (_•_ : Op₂) (ε : carrier) (_⁻¹ : Op₁) : Set where
  infixl 7 _-_
  field
    isMonoid  : IsMonoid _•_ ε
    inverse   : Inverse ε _⁻¹ _•_
    ⁻¹-pres-≈ : _⁻¹ Preserves-≈

  open IsMonoid isMonoid public

  _-_ : Op₂
  x - y = x • (y ⁻¹)

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

record IsNearSemiring (+ * : Op₂) (0# : carrier) : Set where
  field
    +-isMonoid    : IsMonoid + 0#
    *-isSemigroup : IsSemigroup *
    distribʳ      : * DistributesOverʳ +
    zeroˡ         : LeftZero 0# *

  open IsMonoid +-isMonoid public
         renaming ( assoc       to +-assoc
                  ; •-pres-≈    to +-pres-≈
                  ; isSemigroup to +-isSemigroup
                  ; identity    to +-identity
                  )

  open IsSemigroup *-isSemigroup public
         renaming ( assoc    to *-assoc
                  ; •-pres-≈ to *-pres-≈
                  )

record IsSemiringWithoutOne (+ * : Op₂) (0# : carrier) : Set where
  field
    +-isCommutativeMonoid : IsCommutativeMonoid + 0#
    *-isSemigroup         : IsSemigroup *
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

  open IsSemigroup *-isSemigroup public
         renaming ( assoc       to *-assoc
                  ; •-pres-≈    to *-pres-≈
                  )

  isNearSemiring : IsNearSemiring + * 0#
  isNearSemiring = record
    { +-isMonoid    = +-isMonoid
    ; *-isSemigroup = *-isSemigroup
    ; distribʳ      = proj₂ distrib
    ; zeroˡ         = proj₁ zero
    }

record IsSemiringWithoutAnnihilatingZero (+ * : Op₂) (0# 1# : carrier)
         : Set where
  field
    -- Note that these structures do have an additive unit, but this
    -- unit does not necessarily annihilate multiplication.
    +-isCommutativeMonoid : IsCommutativeMonoid + 0#
    *-isMonoid            : IsMonoid * 1#
    distrib               : * DistributesOver +

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

record IsSemiring (+ * : Op₂) (0# 1# : carrier) : Set where
  field
    isSemiringWithoutAnnihilatingZero :
      IsSemiringWithoutAnnihilatingZero + * 0# 1#
    zero : Zero 0# *

  open IsSemiringWithoutAnnihilatingZero
         isSemiringWithoutAnnihilatingZero public

  isSemiringWithoutOne : IsSemiringWithoutOne + * 0#
  isSemiringWithoutOne = record
    { +-isCommutativeMonoid = +-isCommutativeMonoid
    ; *-isSemigroup         = *-isSemigroup
    ; distrib               = distrib
    ; zero                  = zero
    }

  open IsSemiringWithoutOne isSemiringWithoutOne public
         using (isNearSemiring)

record IsCommutativeSemiringWithoutOne (+ * : Op₂) (0# : carrier)
         : Set where
  field
    isSemiringWithoutOne : IsSemiringWithoutOne + * 0#
    *-comm               : Commutative *

  open IsSemiringWithoutOne isSemiringWithoutOne public

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

  isCommutativeSemiringWithoutOne :
    IsCommutativeSemiringWithoutOne + * 0#
  isCommutativeSemiringWithoutOne = record
    { isSemiringWithoutOne = isSemiringWithoutOne
    ; *-comm               = *-comm
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
       (0# * x) + ((0# * x)  + - (0# * x))  ≈⟨ sym $ +-assoc _ _ _ ⟩
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
      (x * 0#) + ((x * 0#) + - (x * 0#))  ≈⟨ sym $ +-assoc _ _ _ ⟩
      ((x * 0#) + (x * 0#)) + - (x * 0#)  ≈⟨ sym (proj₁ distrib _ _ _) ⟨ +-pres-≈ ⟩ byDef ⟩
      (x * (0# + 0#)) + - (x * 0#)        ≈⟨ (byDef ⟨ *-pres-≈ ⟩ proj₂ +-identity _)
                                               ⟨ +-pres-≈ ⟩
                                             byDef ⟩
      (x * 0#) + - (x * 0#)               ≈⟨ proj₂ --inverse _ ⟩
      0#                                  ∎

  isSemiringWithoutAnnihilatingZero
    : IsSemiringWithoutAnnihilatingZero _+_ _*_ 0# 1#
  isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = +-isCommutativeMonoid
    ; *-isMonoid            = *-isMonoid
    ; distrib               = distrib
    }

  isSemiring : IsSemiring _+_ _*_ 0# 1#
  isSemiring = record
    { isSemiringWithoutAnnihilatingZero =
        isSemiringWithoutAnnihilatingZero
    ; zero = zero
    }

  open IsSemiring isSemiring public
         using (isNearSemiring; isSemiringWithoutOne)

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

  open IsCommutativeSemiring isCommutativeSemiring public
         using (isCommutativeSemiringWithoutOne)

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
    ∨-∧-distribʳ : ∨ DistributesOverʳ ∧

  open IsLattice isLattice public

record IsBooleanAlgebra (∨ ∧ : Op₂) (¬ : Op₁) (⊤ ⊥ : carrier) : Set where
  field
    isDistributiveLattice : IsDistributiveLattice ∨ ∧
    ∨-complementʳ         : RightInverse ⊤ ¬ ∨
    ∧-complementʳ         : RightInverse ⊥ ¬ ∧
    ¬-pres-≈              : ¬ Preserves-≈

  open IsDistributiveLattice isDistributiveLattice public
