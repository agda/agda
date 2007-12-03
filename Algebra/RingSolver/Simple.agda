------------------------------------------------------------------------
-- Instantiates the ring solver with two copies of the same ring
------------------------------------------------------------------------

open import Algebra.Packaged

module Algebra.RingSolver.Simple (r : AlmostCommRingoid) where

import Algebra.RingSolver as R
import Algebra.Props.AlmostCommRing as A
open A r
open R bareRingoid r -bare-almostComm⟶ public
