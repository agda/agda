------------------------------------------------------------------------
-- Algebraic properties packaged up with operations
------------------------------------------------------------------------

module Algebra.Packaged where

open import Relation.Binary
open import Algebra
import Algebra.Morphism as M
open Setoid

-- I know that groupoid really means something else...

record Groupoid : Set1 where
  setoid : Setoid
  _+_    : Op₂ setoid
  -_     : Op₁ setoid
  0#     : carrier setoid
  group  : Group setoid _+_ 0# -_

record AbelianGroupoid : Set1 where
  setoid       : Setoid
  _+_          : Op₂ setoid
  -_           : Op₁ setoid
  0#           : carrier setoid
  abelianGroup : AbelianGroup setoid _+_ 0# -_

record Semiringoid : Set1 where
  setoid   : Setoid
  _+_      : Op₂ setoid
  _*_      : Op₂ setoid
  0#       : carrier setoid
  1#       : carrier setoid
  semiring : Semiring setoid _+_ _*_ 0# 1#

record CommutativeSemiringoid : Set1 where
  setoid       : Setoid
  _+_          : Op₂ setoid
  _*_          : Op₂ setoid
  0#           : carrier setoid
  1#           : carrier setoid
  commSemiring : CommutativeSemiring setoid _+_ _*_ 0# 1#

record BareRingoid : Set1 where
  setoid         : Setoid
  _+_            : Op₂ setoid
  _*_            : Op₂ setoid
  -_             : Op₁ setoid
  0#             : carrier setoid
  1#             : carrier setoid

private
 module Bare where
  open BareRingoid

  record Ringoid : Set1 where
    bare : BareRingoid
    ring : Ring (setoid bare)
                (_+_ bare) (_*_ bare) (-_ bare)
                (0# bare) (1# bare)

  record CommutativeRingoid : Set1 where
    bare     : BareRingoid
    commRing : CommutativeRing (setoid bare)
                               (_+_ bare) (_*_ bare) (-_ bare)
                               (0# bare) (1# bare)

  record AlmostCommRingoid : Set1 where
    bare           : BareRingoid
    almostCommRing : AlmostCommRing (setoid bare)
                                    (_+_ bare) (_*_ bare) (-_ bare)
                                    (0# bare) (1# bare)

open Bare public

record Latticoid : Set1 where
  setoid  : Setoid
  _∨_     : Op₂ setoid
  _∧_     : Op₂ setoid
  lattice : Lattice setoid _∨_ _∧_

record DistributiveLatticoid : Set1 where
  setoid      : Setoid
  _∨_         : Op₂ setoid
  _∧_         : Op₂ setoid
  distLattice : DistributiveLattice setoid _∨_ _∧_

record BooleanAlgebraoid : Set1 where
  setoid         : Setoid
  _∨_            : Op₂ setoid
  _∧_            : Op₂ setoid
  ¬_             : Op₁ setoid
  ⊤              : carrier setoid
  ⊥              : carrier setoid
  booleanAlgebra : BooleanAlgebra setoid _∨_ _∧_ ¬_ ⊤ ⊥

------------------------------------------------------------------------
-- Some morphisms

_-Bare-AlmostComm⟶_ : BareRingoid -> AlmostCommRingoid -> Set
b -Bare-AlmostComm⟶ a =
  RingHomomorphism B._+_ B._*_ B.-_ B.0# B.1#
                   A._+_ A._*_ A.-_ A.0# A.1#
  where
  module B = BareRingoid b
  module A = AlmostCommRingoid a
  module A = BareRingoid A.bare
  open module MM = M B.setoid A.setoid
