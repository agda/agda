------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

open import Algebra.Packaged

module Algebra.Props.AbelianGroup
  (g : AbelianGroupoid)
  where

open import Relation.Binary
open import Data.Function
open import Data.Product
import Relation.Binary.EqReasoning
import Algebra
import Algebra.Props.Group
open AbelianGroupoid g
open SetoidOps setoid
open Relation.Binary.EqReasoning preorder
open Algebra setoid
open AbelianGroup abelianGroup
open Group group
open Monoid monoid
open Semigroup semigroup

------------------------------------------------------------------------
-- An abelian group is a group

groupoid : Groupoid
groupoid = record
  { setoid = setoid
  ; _+_    = _+_
  ; -_     = -_
  ; 0#     = 0#
  ; group  = group
  }

open Algebra.Props.Group groupoid public

------------------------------------------------------------------------
-- Some properties

abstract

  private
    lemma : forall x y -> ((x + y) + - x) ≈ y
    lemma x y =
                     begin
      (x + y) + - x
                     ∼⟨ comm _ _ ⟨ •-pres-≈ ⟩ byDef ⟩
      (y + x) + - x
                     ∼⟨ sym $ assoc _ _ _ ⟩
      y + (x + - x)
                     ∼⟨ byDef ⟨ •-pres-≈ ⟩ proj₂ inverse _ ⟩
      y + 0#
                     ∼⟨ proj₂ identity _ ⟩
      y
                     ∎

  ¬-+-comm : forall x y -> ((- x) + (- y)) ≈ (- (x + y))
  ¬-+-comm x y =
                                           begin
    (- x) + - y
                                           ∼⟨ comm _ _ ⟩
    (- y) + - x
                                           ∼⟨ sym $ lem ⟨ •-pres-≈ ⟩ byDef ⟩
    (x + ((y + (- (x + y))) + - y)) + - x
                                           ∼⟨ lemma _ _ ⟩
    (y + (- (x + y))) + - y
                                           ∼⟨ lemma _ _ ⟩
    (- (x + y))
                                           ∎
    where
    lem =
                                     begin
      x + ((y + (- (x + y))) + - y)
                                     ∼⟨ assoc _ _ _ ⟩
      (x + (y + (- (x + y)))) + - y
                                     ∼⟨ assoc _ _ _ ⟨ •-pres-≈ ⟩ byDef ⟩
      ((x + y) + (- (x + y))) + - y
                                     ∼⟨ proj₂ inverse _ ⟨ •-pres-≈ ⟩ byDef ⟩
      0# + (- y)
                                     ∼⟨ proj₁ identity _ ⟩
      - y
                                     ∎
