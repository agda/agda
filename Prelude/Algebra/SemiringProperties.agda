------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

open import Prelude.Algebraoid

module Prelude.Algebra.SemiringProperties (r : Semiringoid) where

open import Prelude.Function
private
  open module R = Semiringoid r

------------------------------------------------------------------------
-- A semiring is a bare ring (using identity as the "almost negation")

bareRingoid : BareRingoid
bareRingoid = record
  { setoid   = setoid
  ; _+_      = _+_
  ; _*_      = _*_
  ; -_       = id
  ; 0#       = 0#
  ; 1#       = 1#
  }
