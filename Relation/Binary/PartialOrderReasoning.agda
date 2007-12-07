------------------------------------------------------------------------
-- Convenient syntax for "equational reasoning" using a partial order
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.PartialOrderReasoning (p : Poset) where

open Poset p
import Relation.Binary.PreorderReasoning as PreR
open PreR preorder public renaming (_∼⟨_⟩_ to _≤⟨_⟩_)
