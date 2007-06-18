------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

open import Prelude.Algebraoid

module Prelude.Algebra.AlmostCommRingProperties
  (r : AlmostCommRingoid)
  where

open import Prelude.Function
open import Prelude.BinaryRelation
import Prelude.Algebra
import Prelude.Algebra.CommutativeSemiringProperties as CSProp
import Prelude.PreorderProof as PP
private
  open module R = AlmostCommRingoid r
  open module R = BareRingoid bare
  open module R = Prelude.Algebra setoid
  open module R = AlmostCommRing almostCommRing
  open module S = PP (setoid⟶preSetoid setoid)

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

private module RP = CSProp commSemiringoid hiding (bareRingoid)
open RP public

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
