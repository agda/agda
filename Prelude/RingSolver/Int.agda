------------------------------------------------------------------------
-- Uses the integers as the coefficient set
------------------------------------------------------------------------

open import Prelude.Algebraoid

module Prelude.RingSolver.Int (r : AlmostCommRingoid) where

open import Prelude.Int
import Prelude.RingSolver as R
import Prelude.Algebra.AlmostCommRingProperties as A
private
  open module A' = A r
  module R' = R ℤ-bareRingoid r (ℤ-morphism r)
open R' public
