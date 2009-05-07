------------------------------------------------------------------------
-- Instantiates the ring solver with two copies of the same ring
------------------------------------------------------------------------

open import Algebra.RingSolver.AlmostCommutativeRing

module Algebra.RingSolver.Simple (r : AlmostCommutativeRing) where

open AlmostCommutativeRing r
import Algebra.RingSolver as R
open R rawRing r (-raw-almostCommutative⟶ r) public
