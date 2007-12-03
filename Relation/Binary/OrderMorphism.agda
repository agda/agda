------------------------------------------------------------------------
-- Order morphisms
------------------------------------------------------------------------

module Relation.Binary.OrderMorphism where

open import Relation.Binary
open Poset

record _⇒_ (po₁ po₂ : Poset) : Set where
  field
    fun      : carrier po₁ -> carrier po₂
    monotone : fun Preserves _≤_ po₁ → _≤_ po₂

_⇒-DTO_ : (dto₁ dto₂ : DecTotalOrder) -> Set
dto₁ ⇒-DTO dto₂ = poset dto₁ ⇒ poset dto₂
  where open DecTotalOrder
