------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

open import Algebra.Packaged

module Algebra.Props.CommutativeSemiring
  (r : CommutativeSemiringoid)
  where

import Algebra
import Relation.Binary.EqReasoning
open import Relation.Binary
open import Data.Function
import Algebra.Props.Semiring as SProp
open CommutativeSemiringoid r
open Algebra setoid
open CommutativeSemiring commSemiring
open Relation.Binary.EqReasoning (SetoidOps.preorder setoid)

------------------------------------------------------------------------
-- A commutative semiring is a semiring

semiringoid : Semiringoid
semiringoid = record
  { setoid   = setoid
  ; _+_      = _+_
  ; _*_      = _*_
  ; 0#       = 0#
  ; 1#       = 1#
  ; semiring = semiring
  }

open SProp semiringoid public

------------------------------------------------------------------------
-- Commutative semirings can be viewed as almost commutative rings by
-- using identity as the "almost negation"

almostCommRingoid : AlmostCommRingoid
almostCommRingoid = record
  { bare = bareRingoid
  ; almostCommRing = record
    { commSemiring = commSemiring
    ; ¬-pres-≈     = id
    ; ¬-*-distribˡ = \_ _ -> byDef
    ; ¬-+-comm     = \_ _ -> byDef
    }
  }
