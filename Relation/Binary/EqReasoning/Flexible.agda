------------------------------------------------------------------------
-- Convenient syntax for equational reasoning
------------------------------------------------------------------------

module Relation.Binary.EqReasoning.Flexible where

open import Relation.Binary.PreorderReasoning.Flexible public
  renaming ( _∼⟨_⟩_  to _≈⟨_⟩_
           ; _≈⟨_⟩_  to _≡⟨_⟩_
           )
