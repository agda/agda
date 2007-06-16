------------------------------------------------------------------------
-- Algebraic properties packaged up with operations
------------------------------------------------------------------------

module Prelude.Algebraoid where

open import Prelude.BinaryRelation
open import Prelude.Algebra
open Setoid

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

commSemiringoid⟶semiringoid : CommutativeSemiringoid -> Semiringoid
commSemiringoid⟶semiringoid cs = record
  { setoid   = setoid
  ; _+_      = _+_
  ; _*_      = _*_
  ; 0#       = 0#
  ; 1#       = 1#
  ; semiring = CommutativeSemiring.semiring setoid commSemiring
  }
  where open module CS = CommutativeSemiringoid cs

record Ringoid : Set1 where
  setoid : Setoid
  _+_    : Op₂ setoid
  _*_    : Op₂ setoid
  -_     : Op₁ setoid
  0#     : carrier setoid
  1#     : carrier setoid
  ring   : Ring setoid _+_ _*_ -_ 0# 1#

record Latticoid : Set1 where
  setoid  : Setoid
  _∨_     : Op₂ setoid
  _∧_     : Op₂ setoid
  lattice : Lattice setoid _∨_ _∧_

record BooleanAlgebraoid : Set1 where
  setoid         : Setoid
  _∨_            : Op₂ setoid
  _∧_            : Op₂ setoid
  ¬_             : Op₁ setoid
  ⊤              : carrier setoid
  ⊥              : carrier setoid
  booleanAlgebra : BooleanAlgebra setoid _∨_ _∧_ ¬_ ⊤ ⊥

boolAlgoid⟶latticoid : BooleanAlgebraoid -> Latticoid
boolAlgoid⟶latticoid b = record
  { setoid = setoid
  ; _∨_    = _∨_
  ; _∧_    = _∧_
  ; lattice = BooleanAlgebra.lattice setoid booleanAlgebra
  }
  where open module B = BooleanAlgebraoid b
