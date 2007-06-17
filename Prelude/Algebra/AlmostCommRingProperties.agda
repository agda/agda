------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

open import Prelude.Algebraoid

module Prelude.Algebra.AlmostCommRingProperties
  (r : AlmostCommRingoid)
  where

import Prelude.Algebra
import Prelude.Algebra.CommutativeSemiringProperties
private
  open module R = AlmostCommRingoid r
  open module R = Prelude.Algebra setoid
  open module R = AlmostCommRing almostCommRing

------------------------------------------------------------------------
-- An "almost commutative ring" is a commutative semiring

commSemiringoid : CommutativeSemiringoid
commSemiringoid = record
  { setoid       = setoid
  ; _+_          = _+_
  ; _*_          = _*_
  ; 0#           = 0#
  ; 1#           = 1#
  ; commSemiring = commSemiring
  }

private
  module RP = Prelude.Algebra.CommutativeSemiringProperties
                commSemiringoid
open RP public
