------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

open import Prelude.Algebraoid

module Prelude.Algebra.CommutativeRingProperties
  (r : CommutativeRingoid)
  where

import Prelude.Algebra
import Prelude.Algebra.RingProperties
private
  open module R = CommutativeRingoid r
  open module R = BareRingoid bare
  open module R = Prelude.Algebra setoid
  open module R = CommutativeRing commRing

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

private
  module RP = Prelude.Algebra.RingProperties ringoid
open RP public

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
