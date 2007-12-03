------------------------------------------------------------------------
-- Properties satisfied by total orders
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Props.TotalOrder (t : TotalOrder) where

open Relation.Binary.TotalOrderOps t
open import Relation.Binary.Consequences

decTotalOrder : Decidable _≈_ -> DecTotalOrder
decTotalOrder ≟ = record
  { carrier         = carrier
  ; _≈_             = _≈_
  ; _≤_             = _≤_
  ; isDecTotalOrder = record
      { isTotalOrder = isTotalOrder
      ; _≟_          = ≟
      ; _≤?_         = total+dec⟶dec refl antisym total ≟
      }
  }
