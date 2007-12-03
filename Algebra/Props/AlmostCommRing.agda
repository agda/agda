------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

open import Algebra.Packaged

module Algebra.Props.AlmostCommRing
  (r : AlmostCommRingoid)
  where

open import Data.Function
open import Relation.Binary
import Algebra
import Algebra.Props.CommutativeSemiring as CSProp
import Relation.Binary.EqReasoning as PP
open AlmostCommRingoid r
open BareRingoid bare
open Algebra setoid
open AlmostCommRing almostCommRing
open PP (SetoidOps.preorder setoid)

------------------------------------------------------------------------
-- An "almost commutative ring" is a commutative semiring

commSemiringoid : CommutativeSemiringoid
commSemiringoid = record
  { setoid       = setoid
  ; _+_          = _+_
  ; _*_          = _*_
  ; 0#           = 0#
  ; 1#           = 1#
  ; commSemiring = commSemiring
  }

open CSProp commSemiringoid public hiding (bareRingoid)

------------------------------------------------------------------------
-- An "almost commutative ring" is a bare ring

bareRingoid : BareRingoid
bareRingoid = bare

-bare-almostComm⟶ : bareRingoid -Bare-AlmostComm⟶ r
-bare-almostComm⟶ = record
  { ⟦_⟧    = id
  ; +-homo = \_ _ -> byDef
  ; *-homo = \_ _ -> byDef
  ; ¬-homo = \_ -> byDef
  ; 0-homo = byDef
  ; 1-homo = byDef
  }
