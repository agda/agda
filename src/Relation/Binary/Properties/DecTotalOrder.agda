------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by decidable total orders
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Properties.DecTotalOrder
         {d₁ d₂ d₃} (DT : DecTotalOrder d₁ d₂ d₃) where

open Relation.Binary.DecTotalOrder DT hiding (trans)
import Relation.Binary.NonStrictToStrict as Conv
open Conv _≈_ _≤_

strictTotalOrder : StrictTotalOrder _ _ _
strictTotalOrder = record
  { isStrictTotalOrder = record
      { isEquivalence = isEquivalence
      ; trans         = trans isPartialOrder
      ; compare       = trichotomous Eq.sym _≟_ antisym total
      }
  }

open StrictTotalOrder strictTotalOrder public
