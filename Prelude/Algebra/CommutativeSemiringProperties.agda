------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

open import Prelude.Algebraoid

module Prelude.Algebra.CommutativeSemiringProperties
  (r : CommutativeSemiringoid)
  where

import Prelude.Algebra
import Prelude.PreorderProof
open import Prelude.BinaryRelation
open import Prelude.Function
private
  open module R = CommutativeSemiringoid r
  open module R = Prelude.Algebra setoid
  open module R = CommutativeSemiring commSemiring
  open module S = Prelude.PreorderProof (setoid⟶preSetoid setoid)

------------------------------------------------------------------------
-- A commutative semiring is a semiring

semiringoid : Semiringoid
semiringoid = record
  { setoid   = setoid
  ; _+_      = _+_
  ; _*_      = _*_
  ; 0#       = 0#
  ; 1#       = 1#
  ; semiring = semiring
  }

------------------------------------------------------------------------
-- Commutative semirings can be viewed as almost commutative rings by
-- using identity as the "almost negation"

almostCommRingoid : AlmostCommRingoid
almostCommRingoid = record
  { setoid         = setoid
  ; _+_            = _+_
  ; _*_            = _*_
  ; -_             = id
  ; 0#             = 0#
  ; 1#             = 1#
  ; almostCommRing = record
    { commSemiring = commSemiring
    ; ¬-pres-≈     = id
    ; ¬-*-distribˡ = \_ _ -> byDef
    ; ¬-+-comm     = \_ _ -> byDef
    }
  }
