------------------------------------------------------------------------
-- Algebraic properties packaged up with operations
------------------------------------------------------------------------

module Prelude.Algebraoid where

open import Prelude.BinaryRelation
open import Prelude.Algebra
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

record Ringoid : Set1 where
  setoid : Setoid
  _+_    : Op₂ setoid
  _*_    : Op₂ setoid
  -_     : Op₁ setoid
  0#     : carrier setoid
  1#     : carrier setoid
  ring   : Ring setoid _+_ _*_ -_ 0# 1#

record CommutativeRingoid : Set1 where
  setoid   : Setoid
  _+_      : Op₂ setoid
  _*_      : Op₂ setoid
  -_       : Op₁ setoid
  0#       : carrier setoid
  1#       : carrier setoid
  commRing : CommutativeRing setoid _+_ _*_ -_ 0# 1#

record AlmostCommRingoid : Set1 where
  setoid         : Setoid
  _+_            : Op₂ setoid
  _*_            : Op₂ setoid
  -_             : Op₁ setoid
  0#             : carrier setoid
  1#             : carrier setoid
  almostCommRing : AlmostCommRing setoid _+_ _*_ -_ 0# 1#

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
