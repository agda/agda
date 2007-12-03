------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

open import Algebra.Packaged

module Algebra.Props.Semiring (r : Semiringoid) where

open import Data.Function
open Semiringoid r

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
