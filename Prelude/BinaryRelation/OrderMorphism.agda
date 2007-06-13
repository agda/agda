------------------------------------------------------------------------
-- Order morphisms
------------------------------------------------------------------------

module Prelude.BinaryRelation.OrderMorphism where

open import Prelude.BinaryRelation
open Poset
open DecTotOrder

record _⇒_ (po₁ po₂ : Poset) : Set where
  fun  : carrier po₁ -> carrier po₂
  mono : Monotone (_≤_ po₁) (_≤_ po₂) fun

_⇒-DTO_ : (dto₁ dto₂ : DecTotOrder) -> Set
dto₁ ⇒-DTO dto₂ = poset dto₁ ⇒ poset dto₂
