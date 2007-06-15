------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

open import Prelude.Algebraoid

module Prelude.Algebra.LatticeProperties (l : Latticoid) where

open import Prelude.BinaryRelation
open import Prelude.Function
open import Prelude.Product
open Π
import Prelude.PreorderProof
import Prelude.Algebra
private
  open module L = Latticoid l
  open module L = Prelude.Algebra setoid
  open module L = Lattice lattice
  open module S = Setoid setoid
  open module S = Equivalence equiv
  open module S = Prelude.PreorderProof (setoid⟶preSetoid setoid)

abstract
  idempotent-∧ : Idempotent _∧_
  idempotent-∧ x =
    x ∧ x
                       ≃⟨ byDef ⟨ ∧-pres-≈ ⟩ sym (proj₁ absorptive _ _) ⟩
    x ∧ (x ∨ (x ∧ x))
                       ≃⟨ proj₂ absorptive _ _ ⟩
    x
                       ∎

  idempotent-∨ : Idempotent _∨_
  idempotent-∨ x =
    x ∨ x
                 ≃⟨ byDef ⟨ ∨-pres-≈ ⟩ sym (idempotent-∧ _) ⟩
    x ∨ (x ∧ x)
                 ≃⟨ proj₁ absorptive _ _ ⟩
    x
                 ∎
