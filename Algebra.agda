------------------------------------------------------------------------
-- Algebraic structures
------------------------------------------------------------------------

-- Algebraic structures packed up with setoids and operations.

module Algebra where

open import Relation.Binary
import Algebra.FunctionProperties as P
open import Algebra.Structures
open import Data.Function

------------------------------------------------------------------------
-- Semigroups, (commutative) monoids and (abelian) groups

record Semigroup : Set1 where
  infixl 7 _∙_
  field
    setoid      : Setoid
    _∙_         : P.Op₂ setoid
    isSemigroup : IsSemigroup setoid _∙_

  open Setoid setoid public
  open IsSemigroup setoid isSemigroup public

-- A raw monoid is a monoid without any laws (except for the
-- underlying equality).

record RawMonoid : Set1 where
  infixl 7 _∙_
  field
    setoid : Setoid
    _∙_    : P.Op₂ setoid
    ε      : Setoid.carrier setoid

  open Setoid setoid public

record Monoid : Set1 where
  infixl 7 _∙_
  field
    setoid   : Setoid
    _∙_      : P.Op₂ setoid
    ε        : Setoid.carrier setoid
    isMonoid : IsMonoid setoid _∙_ ε

  open Setoid setoid public
  open IsMonoid setoid isMonoid public

  semigroup : Semigroup
  semigroup = record
    { setoid      = setoid
    ; _∙_         = _∙_
    ; isSemigroup = isSemigroup
    }

  rawMonoid : RawMonoid
  rawMonoid = record
    { setoid = setoid
    ; _∙_    = _∙_
    ; ε      = ε
    }

record CommutativeMonoid : Set1 where
  infixl 7 _∙_
  field
    setoid              : Setoid
    _∙_                 : P.Op₂ setoid
    ε                   : Setoid.carrier setoid
    isCommutativeMonoid : IsCommutativeMonoid setoid _∙_ ε

  open Setoid setoid public
  open IsCommutativeMonoid setoid isCommutativeMonoid public

  monoid : Monoid
  monoid = record
    { setoid   = setoid
    ; _∙_      = _∙_
    ; ε        = ε
    ; isMonoid = isMonoid
    }

  open Setoid setoid public
  open Monoid monoid public using (semigroup; rawMonoid)

record Group : Set1 where
  infix  8 _⁻¹
  infixl 7 _∙_
  field
    setoid  : Setoid
    _∙_     : P.Op₂ setoid
    ε       : Setoid.carrier setoid
    _⁻¹     : P.Op₁ setoid
    isGroup : IsGroup setoid _∙_ ε _⁻¹

  open Setoid setoid public
  open IsGroup setoid isGroup public

  monoid : Monoid
  monoid = record
    { setoid   = setoid
    ; _∙_      = _∙_
    ; ε        = ε
    ; isMonoid = isMonoid
    }

  open Monoid monoid public using (semigroup; rawMonoid)

record AbelianGroup : Set1 where
  infix  8 _⁻¹
  infixl 7 _∙_
  field
    setoid         : Setoid
    _∙_            : P.Op₂ setoid
    ε              : Setoid.carrier setoid
    _⁻¹            : P.Op₁ setoid
    isAbelianGroup : IsAbelianGroup setoid _∙_ ε _⁻¹

  open Setoid setoid public
  open IsAbelianGroup setoid isAbelianGroup public

  group : Group
  group = record
    { setoid  = setoid
    ; _∙_     = _∙_
    ; ε       = ε
    ; _⁻¹     = _⁻¹
    ; isGroup = isGroup
    }

  open Group group public using (semigroup; monoid; rawMonoid)

  commutativeMonoid : CommutativeMonoid
  commutativeMonoid = record
    { setoid              = setoid
    ; _∙_                 = _∙_
    ; ε                   = ε
    ; isCommutativeMonoid = isCommutativeMonoid
    }

------------------------------------------------------------------------
-- Various kinds of semirings

record NearSemiring : Set1 where
  infixl 7 _*_
  infixl 6 _+_
  field
    setoid         : Setoid
    _+_            : P.Op₂ setoid
    _*_            : P.Op₂ setoid
    0#             : Setoid.carrier setoid
    isNearSemiring : IsNearSemiring setoid _+_ _*_ 0#

  open Setoid setoid public
  open IsNearSemiring setoid isNearSemiring public

  +-monoid : Monoid
  +-monoid = record
    { setoid   = setoid
    ; _∙_      = _+_
    ; ε        = 0#
    ; isMonoid = +-isMonoid
    }

  open Monoid +-monoid public
         using () renaming ( semigroup to +-semigroup
                           ; rawMonoid to +-rawMonoid)

  *-semigroup : Semigroup
  *-semigroup = record
    { setoid      = setoid
    ; _∙_         = _*_
    ; isSemigroup = *-isSemigroup
    }

record SemiringWithoutOne : Set1 where
  infixl 7 _*_
  infixl 6 _+_
  field
    setoid               : Setoid
    _+_                  : P.Op₂ setoid
    _*_                  : P.Op₂ setoid
    0#                   : Setoid.carrier setoid
    isSemiringWithoutOne : IsSemiringWithoutOne setoid _+_ _*_ 0#

  open Setoid setoid public
  open IsSemiringWithoutOne setoid isSemiringWithoutOne public

  nearSemiring : NearSemiring
  nearSemiring = record
    { setoid         = setoid
    ; _+_            = _+_
    ; _*_            = _*_
    ; 0#             = 0#
    ; isNearSemiring = isNearSemiring
    }

  open NearSemiring nearSemiring public
         using ( +-semigroup; +-rawMonoid; +-monoid
               ; *-semigroup
               )

  +-commutativeMonoid : CommutativeMonoid
  +-commutativeMonoid = record
    { setoid              = setoid
    ; _∙_                 = _+_
    ; ε                   = 0#
    ; isCommutativeMonoid = +-isCommutativeMonoid
    }

record SemiringWithoutAnnihilatingZero : Set1 where
  infixl 7 _*_
  infixl 6 _+_
  field
    setoid                            : Setoid
    _+_                               : P.Op₂ setoid
    _*_                               : P.Op₂ setoid
    0#                                : Setoid.carrier setoid
    1#                                : Setoid.carrier setoid
    isSemiringWithoutAnnihilatingZero :
      IsSemiringWithoutAnnihilatingZero setoid _+_ _*_ 0# 1#

  open Setoid setoid public
  open IsSemiringWithoutAnnihilatingZero
         setoid isSemiringWithoutAnnihilatingZero public

  +-commutativeMonoid : CommutativeMonoid
  +-commutativeMonoid = record
    { setoid              = setoid
    ; _∙_                 = _+_
    ; ε                   = 0#
    ; isCommutativeMonoid = +-isCommutativeMonoid
    }

  open CommutativeMonoid +-commutativeMonoid public using ()
         renaming ( semigroup to +-semigroup
                  ; rawMonoid to +-rawMonoid
                  ; monoid    to +-monoid
                  )

  *-monoid : Monoid
  *-monoid = record
    { setoid   = setoid
    ; _∙_      = _*_
    ; ε        = 1#
    ; isMonoid = *-isMonoid
    }

  open Monoid *-monoid public using ()
         renaming ( semigroup to *-semigroup
                  ; rawMonoid to *-rawMonoid
                  )

record Semiring : Set1 where
  infixl 7 _*_
  infixl 6 _+_
  field
    setoid     : Setoid
    _+_        : P.Op₂ setoid
    _*_        : P.Op₂ setoid
    0#         : Setoid.carrier setoid
    1#         : Setoid.carrier setoid
    isSemiring : IsSemiring setoid _+_ _*_ 0# 1#

  open Setoid setoid public
  open IsSemiring setoid isSemiring public

  semiringWithoutAnnihilatingZero : SemiringWithoutAnnihilatingZero
  semiringWithoutAnnihilatingZero = record
    { setoid                            = setoid
    ; _+_                               = _+_
    ; _*_                               = _*_
    ; 0#                                = 0#
    ; 1#                                = 1#
    ; isSemiringWithoutAnnihilatingZero =
        isSemiringWithoutAnnihilatingZero
    }

  open SemiringWithoutAnnihilatingZero
         semiringWithoutAnnihilatingZero public
         using ( +-semigroup; +-rawMonoid; +-monoid
               ; +-commutativeMonoid
               ; *-semigroup; *-rawMonoid; *-monoid
               )

  semiringWithoutOne : SemiringWithoutOne
  semiringWithoutOne = record
    { setoid               = setoid
    ; _+_                  = _+_
    ; _*_                  = _*_
    ; 0#                   = 0#
    ; isSemiringWithoutOne = isSemiringWithoutOne
    }

  open SemiringWithoutOne semiringWithoutOne public
         using (nearSemiring)

record CommutativeSemiringWithoutOne : Set1 where
  infixl 7 _*_
  infixl 6 _+_
  field
    setoid                          : Setoid
    _+_                             : P.Op₂ setoid
    _*_                             : P.Op₂ setoid
    0#                              : Setoid.carrier setoid
    isCommutativeSemiringWithoutOne :
      IsCommutativeSemiringWithoutOne setoid _+_ _*_ 0#

  open Setoid setoid public
  open IsCommutativeSemiringWithoutOne
         setoid isCommutativeSemiringWithoutOne public

  semiringWithoutOne : SemiringWithoutOne
  semiringWithoutOne = record
    { setoid               = setoid
    ; _+_                  = _+_
    ; _*_                  = _*_
    ; 0#                   = 0#
    ; isSemiringWithoutOne = isSemiringWithoutOne
    }

  open SemiringWithoutOne semiringWithoutOne public
         using ( +-semigroup; +-rawMonoid; +-monoid
               ; +-commutativeMonoid
               ; *-semigroup
               ; nearSemiring
               )

record CommutativeSemiring : Set1 where
  infixl 7 _*_
  infixl 6 _+_
  field
    setoid                : Setoid
    _+_                   : P.Op₂ setoid
    _*_                   : P.Op₂ setoid
    0#                    : Setoid.carrier setoid
    1#                    : Setoid.carrier setoid
    isCommutativeSemiring : IsCommutativeSemiring setoid _+_ _*_ 0# 1#

  open Setoid setoid public
  open IsCommutativeSemiring setoid isCommutativeSemiring public

  semiring : Semiring
  semiring = record
    { setoid     = setoid
    ; _+_        = _+_
    ; _*_        = _*_
    ; 0#         = 0#
    ; 1#         = 1#
    ; isSemiring = isSemiring
    }

  open Semiring semiring public
         using ( +-semigroup; +-rawMonoid; +-monoid
               ; +-commutativeMonoid
               ; *-semigroup; *-rawMonoid; *-monoid
               ; nearSemiring; semiringWithoutOne
               ; semiringWithoutAnnihilatingZero
               )

  *-commutativeMonoid : CommutativeMonoid
  *-commutativeMonoid = record
    { setoid              = setoid
    ; _∙_                 = _*_
    ; ε                   = 1#
    ; isCommutativeMonoid = *-isCommutativeMonoid
    }

  commutativeSemiringWithoutOne : CommutativeSemiringWithoutOne
  commutativeSemiringWithoutOne = record
    { setoid                          = setoid
    ; _+_                             = _+_
    ; _*_                             = _*_
    ; 0#                              = 0#
    ; isCommutativeSemiringWithoutOne = isCommutativeSemiringWithoutOne
    }

------------------------------------------------------------------------
-- (Commutative) rings

-- A raw ring is a ring without any laws (except for the underlying
-- equality).

record RawRing : Set1 where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  field
    setoid : Setoid
    _+_    : P.Op₂ setoid
    _*_    : P.Op₂ setoid
    -_     : P.Op₁ setoid
    0#     : Setoid.carrier setoid
    1#     : Setoid.carrier setoid

  open Setoid setoid public

record Ring : Set1 where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  field
    setoid : Setoid
    _+_    : P.Op₂ setoid
    _*_    : P.Op₂ setoid
    -_     : P.Op₁ setoid
    0#     : Setoid.carrier setoid
    1#     : Setoid.carrier setoid
    isRing : IsRing setoid _+_ _*_ -_ 0# 1#

  open Setoid setoid public
  open IsRing setoid isRing public

  +-abelianGroup : AbelianGroup
  +-abelianGroup = record
    { setoid         = setoid
    ; _∙_            = _+_
    ; ε              = 0#
    ; _⁻¹            = -_
    ; isAbelianGroup = +-isAbelianGroup
    }

  semiring : Semiring
  semiring = record
    { setoid     = setoid
    ; _+_        = _+_
    ; _*_        = _*_
    ; 0#         = 0#
    ; 1#         = 1#
    ; isSemiring = isSemiring
    }

  open Semiring semiring public
         using ( +-semigroup; +-rawMonoid; +-monoid
               ; +-commutativeMonoid
               ; *-semigroup; *-rawMonoid; *-monoid
               ; nearSemiring; semiringWithoutOne
               ; semiringWithoutAnnihilatingZero
               )

  rawRing : RawRing
  rawRing = record
    { setoid = setoid
    ; _+_    = _+_
    ; _*_    = _*_
    ; -_     = -_
    ; 0#     = 0#
    ; 1#     = 1#
    }

record CommutativeRing : Set1 where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  field
    setoid            : Setoid
    _+_               : P.Op₂ setoid
    _*_               : P.Op₂ setoid
    -_                : P.Op₁ setoid
    0#                : Setoid.carrier setoid
    1#                : Setoid.carrier setoid
    isCommutativeRing : IsCommutativeRing setoid _+_ _*_ -_ 0# 1#

  open Setoid setoid public
  open IsCommutativeRing setoid isCommutativeRing public

  ring : Ring
  ring = record
    { setoid = setoid
    ; _+_    = _+_
    ; _*_    = _*_
    ; -_     = -_
    ; 0#     = 0#
    ; 1#     = 1#
    ; isRing = isRing
    }

  commutativeSemiring : CommutativeSemiring
  commutativeSemiring = record
    { setoid                = setoid
    ; _+_                   = _+_
    ; _*_                   = _*_
    ; 0#                    = 0#
    ; 1#                    = 1#
    ; isCommutativeSemiring = isCommutativeSemiring
    }

  open Ring ring public using (rawRing; +-abelianGroup)
  open CommutativeSemiring commutativeSemiring public
         using ( +-semigroup; +-rawMonoid; +-monoid; +-commutativeMonoid
               ; *-semigroup; *-rawMonoid; *-monoid; *-commutativeMonoid
               ; nearSemiring; semiringWithoutOne
               ; semiringWithoutAnnihilatingZero; semiring
               ; commutativeSemiringWithoutOne
               )

------------------------------------------------------------------------
-- (Distributive) lattices and boolean algebras

record Lattice : Set1 where
  infixr 7 _∧_
  infixr 6 _∨_
  field
    setoid    : Setoid
    _∨_       : P.Op₂ setoid
    _∧_       : P.Op₂ setoid
    isLattice : IsLattice setoid _∨_ _∧_

  open Setoid setoid public
  open IsLattice setoid isLattice public

record DistributiveLattice : Set1 where
  infixr 7 _∧_
  infixr 6 _∨_
  field
    setoid                : Setoid
    _∨_                   : P.Op₂ setoid
    _∧_                   : P.Op₂ setoid
    isDistributiveLattice : IsDistributiveLattice setoid _∨_ _∧_

  open Setoid setoid public
  open IsDistributiveLattice setoid isDistributiveLattice public

  lattice : Lattice
  lattice = record
    { setoid    = setoid
    ; _∨_       = _∨_
    ; _∧_       = _∧_
    ; isLattice = isLattice
    }

record BooleanAlgebra : Set1 where
  infix  8 ¬_
  infixr 7 _∧_
  infixr 6 _∨_
  field
    setoid           : Setoid
    _∨_              : P.Op₂ setoid
    _∧_              : P.Op₂ setoid
    ¬_               : P.Op₁ setoid
    ⊤                : Setoid.carrier setoid
    ⊥                : Setoid.carrier setoid
    isBooleanAlgebra : IsBooleanAlgebra setoid _∨_ _∧_ ¬_ ⊤ ⊥

  open Setoid setoid public
  open IsBooleanAlgebra setoid isBooleanAlgebra public

  distributiveLattice : DistributiveLattice
  distributiveLattice = record
    { setoid                = setoid
    ; _∨_                   = _∨_
    ; _∧_                   = _∧_
    ; isDistributiveLattice = isDistributiveLattice
    }

  open DistributiveLattice distributiveLattice public
         using (lattice)
