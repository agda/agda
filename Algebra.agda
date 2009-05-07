------------------------------------------------------------------------
-- Definitions of algebraic structures like monoids and rings
-- (packed in records together with sets, operations, etc.)
------------------------------------------------------------------------

module Algebra where

open import Relation.Binary
open import Algebra.FunctionProperties
open import Algebra.Structures
open import Data.Function

------------------------------------------------------------------------
-- Semigroups, (commutative) monoids and (abelian) groups

record Semigroup : Set₁ where
  infixl 7 _∙_
  infix  4 _≈_
  field
    carrier     : Set
    _≈_         : Rel carrier
    _∙_         : Op₂ carrier
    isSemigroup : IsSemigroup _≈_ _∙_

  open IsSemigroup isSemigroup public

  setoid : Setoid
  setoid = record { isEquivalence = isEquivalence }

-- A raw monoid is a monoid without any laws.

record RawMonoid : Set₁ where
  infixl 7 _∙_
  infix  4 _≈_
  field
    carrier : Set
    _≈_     : Rel carrier
    _∙_     : Op₂ carrier
    ε       : carrier

record Monoid : Set₁ where
  infixl 7 _∙_
  infix  4 _≈_
  field
    carrier  : Set
    _≈_      : Rel carrier
    _∙_      : Op₂ carrier
    ε        : carrier
    isMonoid : IsMonoid _≈_ _∙_ ε

  open IsMonoid isMonoid public

  semigroup : Semigroup
  semigroup = record { isSemigroup = isSemigroup }

  open Semigroup semigroup public using (setoid)

  rawMonoid : RawMonoid
  rawMonoid = record
    { _≈_ = _≈_
    ; _∙_ = _∙_
    ; ε   = ε
    }

record CommutativeMonoid : Set₁ where
  infixl 7 _∙_
  infix  4 _≈_
  field
    carrier             : Set
    _≈_                 : Rel carrier
    _∙_                 : Op₂ carrier
    ε                   : carrier
    isCommutativeMonoid : IsCommutativeMonoid _≈_ _∙_ ε

  open IsCommutativeMonoid isCommutativeMonoid public

  monoid : Monoid
  monoid = record { isMonoid = isMonoid }

  open Monoid monoid public using (setoid; semigroup; rawMonoid)

record Group : Set₁ where
  infix  8 _⁻¹
  infixl 7 _∙_
  infix  4 _≈_
  field
    carrier : Set
    _≈_     : Rel carrier
    _∙_     : Op₂ carrier
    ε       : carrier
    _⁻¹     : Op₁ carrier
    isGroup : IsGroup _≈_ _∙_ ε _⁻¹

  open IsGroup isGroup public

  monoid : Monoid
  monoid = record { isMonoid = isMonoid }

  open Monoid monoid public using (setoid; semigroup; rawMonoid)

record AbelianGroup : Set₁ where
  infix  8 _⁻¹
  infixl 7 _∙_
  infix  4 _≈_
  field
    carrier        : Set
    _≈_            : Rel carrier
    _∙_            : Op₂ carrier
    ε              : carrier
    _⁻¹            : Op₁ carrier
    isAbelianGroup : IsAbelianGroup _≈_ _∙_ ε _⁻¹

  open IsAbelianGroup isAbelianGroup public

  group : Group
  group = record { isGroup = isGroup }

  open Group group public using (setoid; semigroup; monoid; rawMonoid)

  commutativeMonoid : CommutativeMonoid
  commutativeMonoid =
    record { isCommutativeMonoid = isCommutativeMonoid }

------------------------------------------------------------------------
-- Various kinds of semirings

record NearSemiring : Set₁ where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    carrier        : Set
    _≈_            : Rel carrier
    _+_            : Op₂ carrier
    _*_            : Op₂ carrier
    0#             : carrier
    isNearSemiring : IsNearSemiring _≈_ _+_ _*_ 0#

  open IsNearSemiring isNearSemiring public

  +-monoid : Monoid
  +-monoid = record { isMonoid = +-isMonoid }

  open Monoid +-monoid public
         using (setoid)
         renaming ( semigroup to +-semigroup
                  ; rawMonoid to +-rawMonoid)

  *-semigroup : Semigroup
  *-semigroup = record { isSemigroup = *-isSemigroup }

record SemiringWithoutOne : Set₁ where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    carrier              : Set
    _≈_                  : Rel carrier
    _+_                  : Op₂ carrier
    _*_                  : Op₂ carrier
    0#                   : carrier
    isSemiringWithoutOne : IsSemiringWithoutOne _≈_ _+_ _*_ 0#

  open IsSemiringWithoutOne isSemiringWithoutOne public

  nearSemiring : NearSemiring
  nearSemiring = record { isNearSemiring = isNearSemiring }

  open NearSemiring nearSemiring public
         using ( setoid
               ; +-semigroup; +-rawMonoid; +-monoid
               ; *-semigroup
               )

  +-commutativeMonoid : CommutativeMonoid
  +-commutativeMonoid =
    record { isCommutativeMonoid = +-isCommutativeMonoid }

record SemiringWithoutAnnihilatingZero : Set₁ where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    carrier                           : Set
    _≈_                               : Rel carrier
    _+_                               : Op₂ carrier
    _*_                               : Op₂ carrier
    0#                                : carrier
    1#                                : carrier
    isSemiringWithoutAnnihilatingZero :
      IsSemiringWithoutAnnihilatingZero _≈_ _+_ _*_ 0# 1#

  open IsSemiringWithoutAnnihilatingZero
         isSemiringWithoutAnnihilatingZero public

  +-commutativeMonoid : CommutativeMonoid
  +-commutativeMonoid =
    record { isCommutativeMonoid = +-isCommutativeMonoid }

  open CommutativeMonoid +-commutativeMonoid public
         using (setoid)
         renaming ( semigroup to +-semigroup
                  ; rawMonoid to +-rawMonoid
                  ; monoid    to +-monoid
                  )

  *-monoid : Monoid
  *-monoid = record { isMonoid = *-isMonoid }

  open Monoid *-monoid public
         using ()
         renaming ( semigroup to *-semigroup
                  ; rawMonoid to *-rawMonoid
                  )

record Semiring : Set₁ where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    carrier    : Set
    _≈_        : Rel carrier
    _+_        : Op₂ carrier
    _*_        : Op₂ carrier
    0#         : carrier
    1#         : carrier
    isSemiring : IsSemiring _≈_ _+_ _*_ 0# 1#

  open IsSemiring isSemiring public

  semiringWithoutAnnihilatingZero : SemiringWithoutAnnihilatingZero
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

  semiringWithoutOne : SemiringWithoutOne
  semiringWithoutOne =
    record { isSemiringWithoutOne = isSemiringWithoutOne }

  open SemiringWithoutOne semiringWithoutOne public
         using (nearSemiring)

record CommutativeSemiringWithoutOne : Set₁ where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    carrier                         : Set
    _≈_                             : Rel carrier
    _+_                             : Op₂ carrier
    _*_                             : Op₂ carrier
    0#                              : carrier
    isCommutativeSemiringWithoutOne :
      IsCommutativeSemiringWithoutOne _≈_ _+_ _*_ 0#

  open IsCommutativeSemiringWithoutOne
         isCommutativeSemiringWithoutOne public

  semiringWithoutOne : SemiringWithoutOne
  semiringWithoutOne =
    record { isSemiringWithoutOne = isSemiringWithoutOne }

  open SemiringWithoutOne semiringWithoutOne public
         using ( setoid
               ; +-semigroup; +-rawMonoid; +-monoid
               ; +-commutativeMonoid
               ; *-semigroup
               ; nearSemiring
               )

record CommutativeSemiring : Set₁ where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    carrier               : Set
    _≈_                   : Rel carrier
    _+_                   : Op₂ carrier
    _*_                   : Op₂ carrier
    0#                    : carrier
    1#                    : carrier
    isCommutativeSemiring : IsCommutativeSemiring _≈_ _+_ _*_ 0# 1#

  open IsCommutativeSemiring isCommutativeSemiring public

  semiring : Semiring
  semiring = record { isSemiring = isSemiring }

  open Semiring semiring public
         using ( setoid
               ; +-semigroup; +-rawMonoid; +-monoid
               ; +-commutativeMonoid
               ; *-semigroup; *-rawMonoid; *-monoid
               ; nearSemiring; semiringWithoutOne
               ; semiringWithoutAnnihilatingZero
               )

  *-commutativeMonoid : CommutativeMonoid
  *-commutativeMonoid =
    record { isCommutativeMonoid = *-isCommutativeMonoid }

  commutativeSemiringWithoutOne : CommutativeSemiringWithoutOne
  commutativeSemiringWithoutOne = record
    { isCommutativeSemiringWithoutOne = isCommutativeSemiringWithoutOne
    }

------------------------------------------------------------------------
-- (Commutative) rings

-- A raw ring is a ring without any laws.

record RawRing : Set₁ where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    carrier : Set
    _≈_     : Rel carrier
    _+_     : Op₂ carrier
    _*_     : Op₂ carrier
    -_      : Op₁ carrier
    0#      : carrier
    1#      : carrier

record Ring : Set₁ where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    carrier : Set
    _≈_     : Rel carrier
    _+_     : Op₂ carrier
    _*_     : Op₂ carrier
    -_      : Op₁ carrier
    0#      : carrier
    1#      : carrier
    isRing  : IsRing _≈_ _+_ _*_ -_ 0# 1#

  open IsRing isRing public

  +-abelianGroup : AbelianGroup
  +-abelianGroup = record { isAbelianGroup = +-isAbelianGroup }

  semiring : Semiring
  semiring = record { isSemiring = isSemiring }

  open Semiring semiring public
         using ( setoid
               ; +-semigroup; +-rawMonoid; +-monoid
               ; +-commutativeMonoid
               ; *-semigroup; *-rawMonoid; *-monoid
               ; nearSemiring; semiringWithoutOne
               ; semiringWithoutAnnihilatingZero
               )

  rawRing : RawRing
  rawRing = record
    { _≈_ = _≈_
    ; _+_ = _+_
    ; _*_ = _*_
    ; -_  = -_
    ; 0#  = 0#
    ; 1#  = 1#
    }

record CommutativeRing : Set₁ where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    carrier           : Set
    _≈_               : Rel carrier
    _+_               : Op₂ carrier
    _*_               : Op₂ carrier
    -_                : Op₁ carrier
    0#                : carrier
    1#                : carrier
    isCommutativeRing : IsCommutativeRing _≈_ _+_ _*_ -_ 0# 1#

  open IsCommutativeRing isCommutativeRing public

  ring : Ring
  ring = record { isRing = isRing }

  commutativeSemiring : CommutativeSemiring
  commutativeSemiring =
    record { isCommutativeSemiring = isCommutativeSemiring }

  open Ring ring public using (rawRing; +-abelianGroup)
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

record Lattice : Set₁ where
  infixr 7 _∧_
  infixr 6 _∨_
  infix  4 _≈_
  field
    carrier   : Set
    _≈_       : Rel carrier
    _∨_       : Op₂ carrier
    _∧_       : Op₂ carrier
    isLattice : IsLattice _≈_ _∨_ _∧_

  open IsLattice isLattice public

  setoid : Setoid
  setoid = record { isEquivalence = isEquivalence }

record DistributiveLattice : Set₁ where
  infixr 7 _∧_
  infixr 6 _∨_
  infix  4 _≈_
  field
    carrier               : Set
    _≈_                   : Rel carrier
    _∨_                   : Op₂ carrier
    _∧_                   : Op₂ carrier
    isDistributiveLattice : IsDistributiveLattice _≈_ _∨_ _∧_

  open IsDistributiveLattice isDistributiveLattice public

  lattice : Lattice
  lattice = record { isLattice = isLattice }

  open Lattice lattice public using (setoid)

record BooleanAlgebra : Set₁ where
  infix  8 ¬_
  infixr 7 _∧_
  infixr 6 _∨_
  infix  4 _≈_
  field
    carrier          : Set
    _≈_              : Rel carrier
    _∨_              : Op₂ carrier
    _∧_              : Op₂ carrier
    ¬_               : Op₁ carrier
    ⊤                : carrier
    ⊥                : carrier
    isBooleanAlgebra : IsBooleanAlgebra _≈_ _∨_ _∧_ ¬_ ⊤ ⊥

  open IsBooleanAlgebra isBooleanAlgebra public

  distributiveLattice : DistributiveLattice
  distributiveLattice =
    record { isDistributiveLattice = isDistributiveLattice }

  open DistributiveLattice distributiveLattice public
         using (setoid; lattice)
