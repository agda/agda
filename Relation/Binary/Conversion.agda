------------------------------------------------------------------------
-- Code for converting between various structures
------------------------------------------------------------------------

module Relation.Binary.Conversion where

open import Logic
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

setoid⟶preSetoid : Setoid -> PreSetoid
setoid⟶preSetoid s = record
  { carrier  = carrier
  ; _∼_      = _≈_
  ; _≈_      = _≡_
  ; preorder = preorder
  ; equiv    = ≡-equivalence
  }
  where
  open module S = Setoid s
  open module E = Equivalence equiv

poset⟶preSetoid : Poset -> PreSetoid
poset⟶preSetoid p = record
  { carrier  = carrier
  ; _∼_      = _≤_
  ; _≈_      = _≈_
  ; preorder = preorder
  ; equiv    = equiv
  }
  where
  open module P = Poset p
  open module P = PartialOrder P.ord
