------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

open import Algebra.Packaged

module Algebra.Props.Lattice (l : Latticoid) where

open import Relation.Binary
open import Data.Function
open import Data.Product
import Relation.Binary.EqReasoning
import Algebra
private
  open module L = Latticoid l
  open module L = Algebra setoid
  open module L = Lattice lattice
  open module S = Setoid setoid
  open module S = Equivalence equiv
  open module S = Relation.Binary.EqReasoning (setoid⟶preSetoid setoid)

abstract

  -- The dual construction is also a lattice.

  ∧-∨-lattice : Lattice _∧_ _∨_
  ∧-∨-lattice = record
    { ∨-comm     = ∧-comm
    ; ∨-assoc    = ∧-assoc
    ; ∨-pres-≈   = ∧-pres-≈
    ; ∧-comm     = ∨-comm
    ; ∧-assoc    = ∨-assoc
    ; ∧-pres-≈   = ∨-pres-≈
    ; absorptive = swap absorptive
    }

  ∧-idempotent : Idempotent _∧_
  ∧-idempotent x =
    x ∧ x
                       ≃⟨ byDef ⟨ ∧-pres-≈ ⟩ sym (proj₁ absorptive _ _) ⟩
    x ∧ (x ∨ (x ∧ x))
                       ≃⟨ proj₂ absorptive _ _ ⟩
    x
                       ∎

  ∨-idempotent : Idempotent _∨_
  ∨-idempotent x =
    x ∨ x
                 ≃⟨ byDef ⟨ ∨-pres-≈ ⟩ sym (∧-idempotent _) ⟩
    x ∨ (x ∧ x)
                 ≃⟨ proj₁ absorptive _ _ ⟩
    x
                 ∎
