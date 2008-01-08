------------------------------------------------------------------------
-- Convenient syntax for "equational reasoning" using a partial order
------------------------------------------------------------------------

module Relation.Binary.PartialOrderReasoning.Flexible where

open import Relation.Binary.PreorderReasoning.Flexible public
  renaming (_∼⟨_⟩_ to _≤⟨_⟩_)
