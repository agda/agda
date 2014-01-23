------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by total orders
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Properties.TotalOrder
         {t₁ t₂ t₃} (T : TotalOrder t₁ t₂ t₃) where

open Relation.Binary.TotalOrder T
open import Relation.Binary.Consequences

decTotalOrder : Decidable _≈_ → DecTotalOrder _ _ _
decTotalOrder ≟ = record
  { isDecTotalOrder = record
      { isTotalOrder = isTotalOrder
      ; _≟_          = ≟
      ; _≤?_         = total+dec⟶dec reflexive antisym total ≟
      }
  }
