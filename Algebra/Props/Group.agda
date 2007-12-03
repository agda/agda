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
open Groupoid g
open SetoidOps setoid
open Relation.Binary.EqReasoning preorder
open Algebra setoid
open Group group
open Monoid monoid
open Semigroup semigroup

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
