------------------------------------------------------------------------
-- Instantiates the ring solver with two copies of the same ring
------------------------------------------------------------------------

open import Prelude.Algebraoid

module Prelude.RingSolver.Simple (r : AlmostCommRingoid) where

import Prelude.RingSolver as R
import Prelude.Algebra.AlmostCommRingProperties as A
private
  open module A' = A r
  module R' = R bareRingoid r -bare-almostComm⟶
open R' public
