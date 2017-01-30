------------------------------------------------------------------------
-- The Agda standard library
--
-- Some algebraic structures (not packed up with sets, operations,
-- etc.)
------------------------------------------------------------------------

open import Relation.Binary

module Algebra.Structures where

import Algebra.FunctionProperties as FunctionProperties
open import Data.Product
open import Function
open import Level using (_⊔_)
import Relation.Binary.EqReasoning as EqR

open FunctionProperties using (Op₁; Op₂)

------------------------------------------------------------------------
-- One binary operation

record IsSemigroup {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                   (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    isEquivalence : IsEquivalence ≈
    assoc         : Associative ∙
    ∙-cong        : ∙ Preserves₂ ≈ ⟶ ≈ ⟶ ≈

  open IsEquivalence isEquivalence public

record IsMonoid {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    isSemigroup : IsSemigroup ≈ ∙
    identity    : Identity ε ∙

  open IsSemigroup isSemigroup public

record IsCommutativeMonoid {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                           (_∙_ : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    isSemigroup : IsSemigroup ≈ _∙_
    identityˡ   : LeftIdentity ε _∙_
    comm        : Commutative _∙_

  open IsSemigroup isSemigroup public

  identity : Identity ε _∙_
  identity = (identityˡ , identityʳ)
    where
    open EqR (record { isEquivalence = isEquivalence })

    identityʳ : RightIdentity ε _∙_
    identityʳ = λ x → begin
      (x ∙ ε)  ≈⟨ comm x ε ⟩
      (ε ∙ x)  ≈⟨ identityˡ x ⟩
      x        ∎

  isMonoid : IsMonoid ≈ _∙_ ε
  isMonoid = record
    { isSemigroup = isSemigroup
    ; identity    = identity
    }

record IsIdempotentCommutativeMonoid {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                                     (_∙_ : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    isCommutativeMonoid : IsCommutativeMonoid ≈ _∙_ ε
    idem                : Idempotent _∙_

  open IsCommutativeMonoid isCommutativeMonoid public

record IsGroup {a ℓ} {A : Set a} (≈ : Rel A ℓ)
               (_∙_ : Op₂ A) (ε : A) (_⁻¹ : Op₁ A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  infixl 7 _-_
  field
    isMonoid  : IsMonoid ≈ _∙_ ε
    inverse   : Inverse ε _⁻¹ _∙_
    ⁻¹-cong   : _⁻¹ Preserves ≈ ⟶ ≈

  open IsMonoid isMonoid public

  _-_ : FunctionProperties.Op₂ A
  x - y = x ∙ (y ⁻¹)

record IsAbelianGroup
         {a ℓ} {A : Set a} (≈ : Rel A ℓ)
         (∙ : Op₂ A) (ε : A) (⁻¹ : Op₁ A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    isGroup : IsGroup ≈ ∙ ε ⁻¹
    comm    : Commutative ∙

  open IsGroup isGroup public

  isCommutativeMonoid : IsCommutativeMonoid ≈ ∙ ε
  isCommutativeMonoid = record
    { isSemigroup = isSemigroup
    ; identityˡ   = proj₁ identity
    ; comm        = comm
    }

------------------------------------------------------------------------
-- Two binary operations

record IsNearSemiring {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                      (+ * : Op₂ A) (0# : A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    +-isMonoid    : IsMonoid ≈ + 0#
    *-isSemigroup : IsSemigroup ≈ *
    distribʳ      : * DistributesOverʳ +
    zeroˡ         : LeftZero 0# *

  open IsMonoid +-isMonoid public
         renaming ( assoc       to +-assoc
                  ; ∙-cong      to +-cong
                  ; isSemigroup to +-isSemigroup
                  ; identity    to +-identity
                  )

  open IsSemigroup *-isSemigroup public
         using ()
         renaming ( assoc    to *-assoc
                  ; ∙-cong   to *-cong
                  )

record IsSemiringWithoutOne {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                            (+ * : Op₂ A) (0# : A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    +-isCommutativeMonoid : IsCommutativeMonoid ≈ + 0#
    *-isSemigroup         : IsSemigroup ≈ *
    distrib               : * DistributesOver +
    zero                  : Zero 0# *

  open IsCommutativeMonoid +-isCommutativeMonoid public
         hiding (identityˡ)
         renaming ( assoc       to +-assoc
                  ; ∙-cong      to +-cong
                  ; isSemigroup to +-isSemigroup
                  ; identity    to +-identity
                  ; isMonoid    to +-isMonoid
                  ; comm        to +-comm
                  )

  open IsSemigroup *-isSemigroup public
         using ()
         renaming ( assoc       to *-assoc
                  ; ∙-cong      to *-cong
                  )

  isNearSemiring : IsNearSemiring ≈ + * 0#
  isNearSemiring = record
    { +-isMonoid    = +-isMonoid
    ; *-isSemigroup = *-isSemigroup
    ; distribʳ      = proj₂ distrib
    ; zeroˡ         = proj₁ zero
    }

record IsSemiringWithoutAnnihilatingZero
         {a ℓ} {A : Set a} (≈ : Rel A ℓ)
         (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    -- Note that these structures do have an additive unit, but this
    -- unit does not necessarily annihilate multiplication.
    +-isCommutativeMonoid : IsCommutativeMonoid ≈ + 0#
    *-isMonoid            : IsMonoid ≈ * 1#
    distrib               : * DistributesOver +

  open IsCommutativeMonoid +-isCommutativeMonoid public
         hiding (identityˡ)
         renaming ( assoc       to +-assoc
                  ; ∙-cong      to +-cong
                  ; isSemigroup to +-isSemigroup
                  ; identity    to +-identity
                  ; isMonoid    to +-isMonoid
                  ; comm        to +-comm
                  )

  open IsMonoid *-isMonoid public
         using ()
         renaming ( assoc       to *-assoc
                  ; ∙-cong      to *-cong
                  ; isSemigroup to *-isSemigroup
                  ; identity    to *-identity
                  )

record IsSemiring {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                  (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ) where
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
         {a ℓ} {A : Set a} (≈ : Rel A ℓ)
         (+ * : Op₂ A) (0# : A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    isSemiringWithoutOne : IsSemiringWithoutOne ≈ + * 0#
    *-comm               : Commutative *

  open IsSemiringWithoutOne isSemiringWithoutOne public

record IsCommutativeSemiring
         {a ℓ} {A : Set a} (≈ : Rel A ℓ)
         (_+_ _*_ : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    +-isCommutativeMonoid : IsCommutativeMonoid ≈ _+_ 0#
    *-isCommutativeMonoid : IsCommutativeMonoid ≈ _*_ 1#
    distribʳ              : _*_ DistributesOverʳ _+_
    zeroˡ                 : LeftZero 0# _*_

  private
    module +-CM = IsCommutativeMonoid +-isCommutativeMonoid
    open module *-CM = IsCommutativeMonoid *-isCommutativeMonoid public
           using () renaming (comm to *-comm)
  open EqR (record { isEquivalence = +-CM.isEquivalence })

  distrib : _*_ DistributesOver _+_
  distrib = (distribˡ , distribʳ)
    where
    distribˡ : _*_ DistributesOverˡ _+_
    distribˡ x y z = begin
      (x * (y + z))        ≈⟨ *-comm x (y + z) ⟩
      ((y + z) * x)        ≈⟨ distribʳ x y z ⟩
      ((y * x) + (z * x))  ≈⟨ *-comm y x ⟨ +-CM.∙-cong ⟩ *-comm z x ⟩
      ((x * y) + (x * z))  ∎

  zero : Zero 0# _*_
  zero = (zeroˡ , zeroʳ)
    where
    zeroʳ : RightZero 0# _*_
    zeroʳ x = begin
      (x * 0#)  ≈⟨ *-comm x 0# ⟩
      (0# * x)  ≈⟨ zeroˡ x ⟩
      0#        ∎

  isSemiring : IsSemiring ≈ _+_ _*_ 0# 1#
  isSemiring = record
    { isSemiringWithoutAnnihilatingZero = record
      { +-isCommutativeMonoid = +-isCommutativeMonoid
      ; *-isMonoid            = *-CM.isMonoid
      ; distrib               = distrib
      }
    ; zero                              = zero
    }

  open IsSemiring isSemiring public
         hiding (distrib; zero; +-isCommutativeMonoid)

  isCommutativeSemiringWithoutOne :
    IsCommutativeSemiringWithoutOne ≈ _+_ _*_ 0#
  isCommutativeSemiringWithoutOne = record
    { isSemiringWithoutOne = isSemiringWithoutOne
    ; *-comm               = *-CM.comm
    }

record IsRing
         {a ℓ} {A : Set a} (≈ : Rel A ℓ)
         (_+_ _*_ : Op₂ A) (-_ : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    +-isAbelianGroup : IsAbelianGroup ≈ _+_ 0# -_
    *-isMonoid       : IsMonoid ≈ _*_ 1#
    distrib          : _*_ DistributesOver _+_

  open IsAbelianGroup +-isAbelianGroup public
         renaming ( assoc               to +-assoc
                  ; ∙-cong              to +-cong
                  ; isSemigroup         to +-isSemigroup
                  ; identity            to +-identity
                  ; isMonoid            to +-isMonoid
                  ; inverse             to -‿inverse
                  ; ⁻¹-cong             to -‿cong
                  ; isGroup             to +-isGroup
                  ; comm                to +-comm
                  ; isCommutativeMonoid to +-isCommutativeMonoid
                  )

  open IsMonoid *-isMonoid public
         using ()
         renaming ( assoc       to *-assoc
                  ; ∙-cong      to *-cong
                  ; isSemigroup to *-isSemigroup
                  ; identity    to *-identity
                  )

  zero : Zero 0# _*_
  zero = (zeroˡ , zeroʳ)
    where
    open EqR (record { isEquivalence = isEquivalence })

    zeroˡ : LeftZero 0# _*_
    zeroˡ x = begin
        (0# * x)                                ≈⟨ sym $ proj₂ +-identity _ ⟩
       ((0# * x) +            0#)               ≈⟨ refl ⟨ +-cong ⟩ sym (proj₂ -‿inverse _) ⟩
       ((0# * x) + ((0# * x)  + (- (0# * x))))  ≈⟨ sym $ +-assoc _ _ _ ⟩
      (((0# * x) +  (0# * x)) + (- (0# * x)))   ≈⟨ sym (proj₂ distrib _ _ _) ⟨ +-cong ⟩ refl ⟩
             (((0# + 0#) * x) + (- (0# * x)))   ≈⟨ (proj₂ +-identity _ ⟨ *-cong ⟩ refl)
                                                     ⟨ +-cong ⟩
                                                   refl ⟩
                    ((0# * x) + (- (0# * x)))   ≈⟨ proj₂ -‿inverse _ ⟩
                             0#                 ∎

    zeroʳ : RightZero 0# _*_
    zeroʳ x = begin
      (x * 0#)                                ≈⟨ sym $ proj₂ +-identity _ ⟩
      ((x * 0#) + 0#)                         ≈⟨ refl ⟨ +-cong ⟩ sym (proj₂ -‿inverse _) ⟩
      ((x * 0#) + ((x * 0#) + (- (x * 0#))))  ≈⟨ sym $ +-assoc _ _ _ ⟩
      (((x * 0#) + (x * 0#)) + (- (x * 0#)))  ≈⟨ sym (proj₁ distrib _ _ _) ⟨ +-cong ⟩ refl ⟩
      ((x * (0# + 0#)) + (- (x * 0#)))        ≈⟨ (refl ⟨ *-cong ⟩ proj₂ +-identity _)
                                                   ⟨ +-cong ⟩
                                                 refl ⟩
      ((x * 0#) + (- (x * 0#)))               ≈⟨ proj₂ -‿inverse _ ⟩
      0#                                      ∎

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

record IsCommutativeRing
         {a ℓ} {A : Set a} (≈ : Rel A ℓ)
         (+ * : Op₂ A) (- : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    isRing : IsRing ≈ + * - 0# 1#
    *-comm : Commutative *

  open IsRing isRing public

  isCommutativeSemiring : IsCommutativeSemiring ≈ + * 0# 1#
  isCommutativeSemiring = record
    { +-isCommutativeMonoid = +-isCommutativeMonoid
    ; *-isCommutativeMonoid = record
      { isSemigroup = *-isSemigroup
      ; identityˡ   = proj₁ *-identity
      ; comm        = *-comm
      }
    ; distribʳ              = proj₂ distrib
    ; zeroˡ                 = proj₁ zero
    }

  open IsCommutativeSemiring isCommutativeSemiring public
         using ( *-isCommutativeMonoid
               ; isCommutativeSemiringWithoutOne
               )

record IsLattice {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                 (∨ ∧ : Op₂ A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    isEquivalence : IsEquivalence ≈
    ∨-comm        : Commutative ∨
    ∨-assoc       : Associative ∨
    ∨-cong        : ∨ Preserves₂ ≈ ⟶ ≈ ⟶ ≈
    ∧-comm        : Commutative ∧
    ∧-assoc       : Associative ∧
    ∧-cong        : ∧ Preserves₂ ≈ ⟶ ≈ ⟶ ≈
    absorptive    : Absorptive ∨ ∧

  open IsEquivalence isEquivalence public

record IsDistributiveLattice {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                             (∨ ∧ : Op₂ A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    isLattice    : IsLattice ≈ ∨ ∧
    ∨-∧-distribʳ : ∨ DistributesOverʳ ∧

  open IsLattice isLattice public

record IsBooleanAlgebra
         {a ℓ} {A : Set a} (≈ : Rel A ℓ)
         (∨ ∧ : Op₂ A) (¬ : Op₁ A) (⊤ ⊥ : A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    isDistributiveLattice : IsDistributiveLattice ≈ ∨ ∧
    ∨-complementʳ         : RightInverse ⊤ ¬ ∨
    ∧-complementʳ         : RightInverse ⊥ ¬ ∧
    ¬-cong                : ¬ Preserves ≈ ⟶ ≈

  open IsDistributiveLattice isDistributiveLattice public
