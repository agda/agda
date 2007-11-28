------------------------------------------------------------------------
-- Properties satisfied by total orders
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Props.TotalOrder (t : TotalOrder) where

private
  open module T = Relation.Binary.TotalOrderOps t
open import Relation.Binary.Consequences

decTotalOrder : Decidable _≈_ -> DecTotalOrder
decTotalOrder ≟ = record
  { carrier      = carrier
  ; underlyingEq = _≈_
  ; order        = _≤_
  ; isDecTotalOrder = record
      { isTotalOrder = isTotalOrder
      ; ≈-decidable  = ≟
      ; ≤-decidable  = total+dec⟶dec refl antisym total ≟
      }
  }
