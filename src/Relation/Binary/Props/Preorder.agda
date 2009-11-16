------------------------------------------------------------------------
-- Properties satisfied by preorders
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Props.Preorder (p : Preorder) where

open import Data.Function
open import Data.Product as Prod

open Relation.Binary.Preorder p

------------------------------------------------------------------------
-- For every preorder there is an induced equivalence

inducedEquivalence : Setoid
inducedEquivalence = record
  { _≈_           = λ x y → x ∼ y × y ∼ x
  ; isEquivalence = record
    { refl  = (refl , refl)
    ; sym   = swap
    ; trans = Prod.zip trans (flip trans)
    }
  }
