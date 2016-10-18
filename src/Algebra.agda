------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of algebraic structures like monoids and rings
-- (packed in records together with sets, operations, etc.)
------------------------------------------------------------------------

module Algebra where

open import Relation.Binary
open import Algebra.FunctionProperties
open import Algebra.Structures
open import Function
open import Level

------------------------------------------------------------------------
-- Semigroups, (commutative) monoids and (abelian) groups

record Semigroup c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier     : Set c
    _≈_         : Rel Carrier ℓ
    _∙_         : Op₂ Carrier
    isSemigroup : IsSemigroup _≈_ _∙_

  open IsSemigroup isSemigroup public

  setoid : Setoid _ _
  setoid = record { isEquivalence = isEquivalence }

-- A raw monoid is a monoid without any laws.

record RawMonoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    ε       : Carrier

record Monoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier  : Set c
    _≈_      : Rel Carrier ℓ
    _∙_      : Op₂ Carrier
    ε        : Carrier
    isMonoid : IsMonoid _≈_ _∙_ ε

  open IsMonoid isMonoid public

  semigroup : Semigroup _ _
  semigroup = record { isSemigroup = isSemigroup }

  open Semigroup semigroup public using (setoid)

  rawMonoid : RawMonoid _ _
  rawMonoid = record
    { _≈_ = _≈_
    ; _∙_ = _∙_
    ; ε   = ε
    }

record CommutativeMonoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier             : Set c
    _≈_                 : Rel Carrier ℓ
    _∙_                 : Op₂ Carrier
    ε                   : Carrier
    isCommutativeMonoid : IsCommutativeMonoid _≈_ _∙_ ε

  open IsCommutativeMonoid isCommutativeMonoid public

  monoid : Monoid _ _
  monoid = record { isMonoid = isMonoid }

  open Monoid monoid public using (setoid; semigroup; rawMonoid)

record IdempotentCommutativeMonoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier                       : Set c
    _≈_                           : Rel Carrier ℓ
    _∙_                           : Op₂ Carrier
    ε                             : Carrier
    isIdempotentCommutativeMonoid : IsIdempotentCommutativeMonoid _≈_ _∙_ ε

  open IsIdempotentCommutativeMonoid isIdempotentCommutativeMonoid public

  commutativeMonoid : CommutativeMonoid _ _
  commutativeMonoid = record { isCommutativeMonoid = isCommutativeMonoid }

  open CommutativeMonoid commutativeMonoid public
    using (setoid; semigroup; rawMonoid; monoid)

record Group c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 _⁻¹
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    ε       : Carrier
    _⁻¹     : Op₁ Carrier
    isGroup : IsGroup _≈_ _∙_ ε _⁻¹

  open IsGroup isGroup public

  monoid : Monoid _ _
  monoid = record { isMonoid = isMonoid }

  open Monoid monoid public using (setoid; semigroup; rawMonoid)

record AbelianGroup c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 _⁻¹
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier        : Set c
    _≈_            : Rel Carrier ℓ
    _∙_            : Op₂ Carrier
    ε              : Carrier
    _⁻¹            : Op₁ Carrier
    isAbelianGroup : IsAbelianGroup _≈_ _∙_ ε _⁻¹

  open IsAbelianGroup isAbelianGroup public

  group : Group _ _
  group = record { isGroup = isGroup }

  open Group group public using (setoid; semigroup; monoid; rawMonoid)

  commutativeMonoid : CommutativeMonoid _ _
  commutativeMonoid =
    record { isCommutativeMonoid = isCommutativeMonoid }

------------------------------------------------------------------------
-- Various kinds of semirings

record NearSemiring c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier        : Set c
    _≈_            : Rel Carrier ℓ
    _+_            : Op₂ Carrier
    _*_            : Op₂ Carrier
    0#             : Carrier
    isNearSemiring : IsNearSemiring _≈_ _+_ _*_ 0#

  open IsNearSemiring isNearSemiring public

  +-monoid : Monoid _ _
  +-monoid = record { isMonoid = +-isMonoid }

  open Monoid +-monoid public
         using (setoid)
         renaming ( semigroup to +-semigroup
                  ; rawMonoid to +-rawMonoid)

  *-semigroup : Semigroup _ _
  *-semigroup = record { isSemigroup = *-isSemigroup }

record SemiringWithoutOne c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier              : Set c
    _≈_                  : Rel Carrier ℓ
    _+_                  : Op₂ Carrier
    _*_                  : Op₂ Carrier
    0#                   : Carrier
    isSemiringWithoutOne : IsSemiringWithoutOne _≈_ _+_ _*_ 0#

  open IsSemiringWithoutOne isSemiringWithoutOne public

  nearSemiring : NearSemiring _ _
  nearSemiring = record { isNearSemiring = isNearSemiring }

  open NearSemiring nearSemiring public
         using ( setoid
               ; +-semigroup; +-rawMonoid; +-monoid
               ; *-semigroup
               )

  +-commutativeMonoid : CommutativeMonoid _ _
  +-commutativeMonoid =
    record { isCommutativeMonoid = +-isCommutativeMonoid }

record SemiringWithoutAnnihilatingZero c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier                           : Set c
    _≈_                               : Rel Carrier ℓ
    _+_                               : Op₂ Carrier
    _*_                               : Op₂ Carrier
    0#                                : Carrier
    1#                                : Carrier
    isSemiringWithoutAnnihilatingZero :
      IsSemiringWithoutAnnihilatingZero _≈_ _+_ _*_ 0# 1#

  open IsSemiringWithoutAnnihilatingZero
         isSemiringWithoutAnnihilatingZero public

  +-commutativeMonoid : CommutativeMonoid _ _
  +-commutativeMonoid =
    record { isCommutativeMonoid = +-isCommutativeMonoid }

  open CommutativeMonoid +-commutativeMonoid public
         using (setoid)
         renaming ( semigroup to +-semigroup
                  ; rawMonoid to +-rawMonoid
                  ; monoid    to +-monoid
                  )

  *-monoid : Monoid _ _
  *-monoid = record { isMonoid = *-isMonoid }

  open Monoid *-monoid public
         using ()
         renaming ( semigroup to *-semigroup
                  ; rawMonoid to *-rawMonoid
                  )

record Semiring c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier    : Set c
    _≈_        : Rel Carrier ℓ
    _+_        : Op₂ Carrier
    _*_        : Op₂ Carrier
    0#         : Carrier
    1#         : Carrier
    isSemiring : IsSemiring _≈_ _+_ _*_ 0# 1#

  open IsSemiring isSemiring public

  semiringWithoutAnnihilatingZero : SemiringWithoutAnnihilatingZero _ _
  semiringWithoutAnnihilatingZero = record
    { isSemiringWithoutAnnihilatingZero =
        isSemiringWithoutAnnihilatingZero
    }

  open SemiringWithoutAnnihilatingZero
         semiringWithoutAnnihilatingZero public
         using ( setoid
               ; +-semigroup; +-rawMonoid; +-monoid
               ; +-commutativeMonoid
               ; *-semigroup; *-rawMonoid; *-monoid
               )

  semiringWithoutOne : SemiringWithoutOne _ _
  semiringWithoutOne =
    record { isSemiringWithoutOne = isSemiringWithoutOne }

  open SemiringWithoutOne semiringWithoutOne public
         using (nearSemiring)

record CommutativeSemiringWithoutOne c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier                         : Set c
    _≈_                             : Rel Carrier ℓ
    _+_                             : Op₂ Carrier
    _*_                             : Op₂ Carrier
    0#                              : Carrier
    isCommutativeSemiringWithoutOne :
      IsCommutativeSemiringWithoutOne _≈_ _+_ _*_ 0#

  open IsCommutativeSemiringWithoutOne
         isCommutativeSemiringWithoutOne public

  semiringWithoutOne : SemiringWithoutOne _ _
  semiringWithoutOne =
    record { isSemiringWithoutOne = isSemiringWithoutOne }

  open SemiringWithoutOne semiringWithoutOne public
         using ( setoid
               ; +-semigroup; +-rawMonoid; +-monoid
               ; +-commutativeMonoid
               ; *-semigroup
               ; nearSemiring
               )

record CommutativeSemiring c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier               : Set c
    _≈_                   : Rel Carrier ℓ
    _+_                   : Op₂ Carrier
    _*_                   : Op₂ Carrier
    0#                    : Carrier
    1#                    : Carrier
    isCommutativeSemiring : IsCommutativeSemiring _≈_ _+_ _*_ 0# 1#

  open IsCommutativeSemiring isCommutativeSemiring public

  semiring : Semiring _ _
  semiring = record { isSemiring = isSemiring }

  open Semiring semiring public
         using ( setoid
               ; +-semigroup; +-rawMonoid; +-monoid
               ; +-commutativeMonoid
               ; *-semigroup; *-rawMonoid; *-monoid
               ; nearSemiring; semiringWithoutOne
               ; semiringWithoutAnnihilatingZero
               )

  *-commutativeMonoid : CommutativeMonoid _ _
  *-commutativeMonoid =
    record { isCommutativeMonoid = *-isCommutativeMonoid }

  commutativeSemiringWithoutOne : CommutativeSemiringWithoutOne _ _
  commutativeSemiringWithoutOne = record
    { isCommutativeSemiringWithoutOne = isCommutativeSemiringWithoutOne
    }

------------------------------------------------------------------------
-- (Commutative) rings

-- A raw ring is a ring without any laws.

record RawRing c : Set (suc c) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  field
    Carrier : Set c
    _+_     : Op₂ Carrier
    _*_     : Op₂ Carrier
    -_      : Op₁ Carrier
    0#      : Carrier
    1#      : Carrier

record Ring c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _+_     : Op₂ Carrier
    _*_     : Op₂ Carrier
    -_      : Op₁ Carrier
    0#      : Carrier
    1#      : Carrier
    isRing  : IsRing _≈_ _+_ _*_ -_ 0# 1#

  open IsRing isRing public

  +-abelianGroup : AbelianGroup _ _
  +-abelianGroup = record { isAbelianGroup = +-isAbelianGroup }

  semiring : Semiring _ _
  semiring = record { isSemiring = isSemiring }

  open Semiring semiring public
         using ( setoid
               ; +-semigroup; +-rawMonoid; +-monoid
               ; +-commutativeMonoid
               ; *-semigroup; *-rawMonoid; *-monoid
               ; nearSemiring; semiringWithoutOne
               ; semiringWithoutAnnihilatingZero
               )

  open AbelianGroup +-abelianGroup public
         using () renaming (group to +-group)

  rawRing : RawRing _
  rawRing = record
    { _+_ = _+_
    ; _*_ = _*_
    ; -_  = -_
    ; 0#  = 0#
    ; 1#  = 1#
    }

record CommutativeRing c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier           : Set c
    _≈_               : Rel Carrier ℓ
    _+_               : Op₂ Carrier
    _*_               : Op₂ Carrier
    -_                : Op₁ Carrier
    0#                : Carrier
    1#                : Carrier
    isCommutativeRing : IsCommutativeRing _≈_ _+_ _*_ -_ 0# 1#

  open IsCommutativeRing isCommutativeRing public

  ring : Ring _ _
  ring = record { isRing = isRing }

  commutativeSemiring : CommutativeSemiring _ _
  commutativeSemiring =
    record { isCommutativeSemiring = isCommutativeSemiring }

  open Ring ring public using (rawRing; +-group; +-abelianGroup)
  open CommutativeSemiring commutativeSemiring public
         using ( setoid
               ; +-semigroup; +-rawMonoid; +-monoid; +-commutativeMonoid
               ; *-semigroup; *-rawMonoid; *-monoid; *-commutativeMonoid
               ; nearSemiring; semiringWithoutOne
               ; semiringWithoutAnnihilatingZero; semiring
               ; commutativeSemiringWithoutOne
               )

------------------------------------------------------------------------
-- (Distributive) lattices and boolean algebras

record Lattice c ℓ : Set (suc (c ⊔ ℓ)) where
  infixr 7 _∧_
  infixr 6 _∨_
  infix  4 _≈_
  field
    Carrier   : Set c
    _≈_       : Rel Carrier ℓ
    _∨_       : Op₂ Carrier
    _∧_       : Op₂ Carrier
    isLattice : IsLattice _≈_ _∨_ _∧_

  open IsLattice isLattice public

  setoid : Setoid _ _
  setoid = record { isEquivalence = isEquivalence }

record DistributiveLattice c ℓ : Set (suc (c ⊔ ℓ)) where
  infixr 7 _∧_
  infixr 6 _∨_
  infix  4 _≈_
  field
    Carrier               : Set c
    _≈_                   : Rel Carrier ℓ
    _∨_                   : Op₂ Carrier
    _∧_                   : Op₂ Carrier
    isDistributiveLattice : IsDistributiveLattice _≈_ _∨_ _∧_

  open IsDistributiveLattice isDistributiveLattice public

  lattice : Lattice _ _
  lattice = record { isLattice = isLattice }

  open Lattice lattice public using (setoid)

record BooleanAlgebra c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 ¬_
  infixr 7 _∧_
  infixr 6 _∨_
  infix  4 _≈_
  field
    Carrier          : Set c
    _≈_              : Rel Carrier ℓ
    _∨_              : Op₂ Carrier
    _∧_              : Op₂ Carrier
    ¬_               : Op₁ Carrier
    ⊤                : Carrier
    ⊥                : Carrier
    isBooleanAlgebra : IsBooleanAlgebra _≈_ _∨_ _∧_ ¬_ ⊤ ⊥

  open IsBooleanAlgebra isBooleanAlgebra public

  distributiveLattice : DistributiveLattice _ _
  distributiveLattice =
    record { isDistributiveLattice = isDistributiveLattice }

  open DistributiveLattice distributiveLattice public
         using (setoid; lattice)
