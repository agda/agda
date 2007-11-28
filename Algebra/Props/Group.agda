------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

open import Algebra.Packaged

module Algebra.Props.Group (g : Groupoid) where

open import Relation.Binary
open import Data.Function
open import Data.Product
import Relation.Binary.EqReasoning
import Algebra
private
  open module G  = Groupoid g
  open module S  = SetoidOps setoid
  open module PP = Relation.Binary.EqReasoning preorder
  open module G  = Algebra setoid
  open module G  = Group group
  open module G  = Monoid monoid
  open module G  = Semigroup semigroup

------------------------------------------------------------------------
-- Some properties

abstract

  ¬-involutive : forall x -> (- - x) ≈ x
  ¬-involutive x =
                           begin
    - - x
                           ∼⟨ sym $ proj₂ identity _ ⟩
    (- - x) + 0#
                           ∼⟨ byDef ⟨ •-pres-≈ ⟩ sym (proj₁ inverse _) ⟩
    (- - x) + ((- x) + x)
                           ∼⟨ assoc _ _ _ ⟩
    ((- - x) + - x) + x
                           ∼⟨ proj₁ inverse _ ⟨ •-pres-≈ ⟩ byDef ⟩
    0# + x
                           ∼⟨ proj₁ identity _ ⟩
    x
                           ∎
