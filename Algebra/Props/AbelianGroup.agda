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
open import Relation.Binary.Conversion
import Relation.Binary.EqReasoning
import Algebra
import Algebra.Props.Group
private
  open module G  = AbelianGroupoid g
  open module S  = Setoid setoid
  open module E  = Equivalence equiv
  open module PP = Relation.Binary.EqReasoning (setoid⟶preSetoid setoid)
  open module G  = Algebra setoid
  open module G  = AbelianGroup abelianGroup
  open module G  = Group group
  open module G  = Monoid monoid
  open module G  = Semigroup semigroup

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

private
  module GP = Algebra.Props.Group groupoid
open GP public

------------------------------------------------------------------------
-- Some properties

abstract

  private
    lemma : forall x y -> ((x + y) + - x) ≈ y
    lemma x y =
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
