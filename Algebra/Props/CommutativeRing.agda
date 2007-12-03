------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

open import Algebra.Packaged

module Algebra.Props.CommutativeRing
  (r : CommutativeRingoid)
  where

import Algebra
import Algebra.Props.Ring
open CommutativeRingoid r
open BareRingoid bare
open Algebra setoid
open CommutativeRing commRing

------------------------------------------------------------------------
-- A commutative ring is a ring

ringoid : Ringoid
ringoid = record
  { bare = record
    { setoid = setoid
    ; _+_    = _+_
    ; _*_    = _*_
    ; -_     = -_
    ; 0#     = 0#
    ; 1#     = 1#
    }
  ; ring = ring
  }

open Algebra.Props.Ring ringoid public

------------------------------------------------------------------------
-- A commutative ring is a commutative semiring

abstract

  commSemiring : CommutativeSemiring _+_ _*_ 0# 1#
  commSemiring = record
    { semiring = semiring
    ; *-comm   = *-comm
    }

commSemiringoid : CommutativeSemiringoid
commSemiringoid = record
  { setoid       = setoid
  ; _+_          = _+_
  ; _*_          = _*_
  ; 0#           = 0#
  ; 1#           = 1#
  ; commSemiring = commSemiring
  }

------------------------------------------------------------------------
-- A commutative ring is an "almost commutative ring"

abstract

  almostCommRing : AlmostCommRing _+_ _*_ -_ 0# 1#
  almostCommRing = record
    { commSemiring = commSemiring
    ; ¬-pres-≈     = Group.⁻¹-pres-≈ (AbelianGroup.group (Ring.+-group ring))
    ; ¬-*-distribˡ = ¬-*-distribˡ
    ; ¬-+-comm     = ¬-+-comm
    }

almostCommRingoid : AlmostCommRingoid
almostCommRingoid = record
  { bare = record
    { setoid = setoid
    ; _+_    = _+_
    ; _*_    = _*_
    ; -_     = -_
    ; 0#     = 0#
    ; 1#     = 1#
    }
  ; almostCommRing = almostCommRing
  }
