------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

open import Prelude.Algebraoid

module Prelude.Algebra.GroupProperties (g : Groupoid) where

open import Prelude.BinaryRelation
open import Prelude.Function
open import Prelude.Product
open Π
import Prelude.PreorderProof
import Prelude.Algebra
private
  open module G  = Groupoid g
  open module S  = Setoid setoid
  open module E  = Equivalence equiv
  open module PP = Prelude.PreorderProof (setoid⟶preSetoid setoid)
  open module G  = Prelude.Algebra setoid
  open module G  = Group group
  open module G  = Monoid monoid
  open module G  = Semigroup semigroup

------------------------------------------------------------------------
-- Some properties

abstract

  ¬-involutive : forall x -> (- - x) ≈ x
  ¬-involutive x =
    - - x
                           ≃⟨ sym $ proj₂ identity _ ⟩
    (- - x) + 0#
                           ≃⟨ byDef ⟨ •-pres-≈ ⟩ sym (proj₁ inverse _) ⟩
    (- - x) + ((- x) + x)
                           ≃⟨ assoc _ _ _ ⟩
    ((- - x) + - x) + x
                           ≃⟨ proj₁ inverse _ ⟨ •-pres-≈ ⟩ byDef ⟩
    0# + x
                           ≃⟨ proj₁ identity _ ⟩
    x
                           ∎
