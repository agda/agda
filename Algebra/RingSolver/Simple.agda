------------------------------------------------------------------------
-- Instantiates the ring solver with two copies of the same ring
------------------------------------------------------------------------

open import Algebra.Packaged

module Algebra.RingSolver.Simple (r : AlmostCommRingoid) where

import Algebra.RingSolver as R
import Algebra.Props.AlmostCommRing as A
private
  open module A' = A r
  module R' = R bareRingoid r -bare-almostComm⟶
open R' public
