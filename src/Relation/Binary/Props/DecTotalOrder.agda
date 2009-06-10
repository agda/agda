------------------------------------------------------------------------
-- Properties satisfied by decidable total orders
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Props.DecTotalOrder (dt : DecTotalOrder) where

open Relation.Binary.DecTotalOrder dt hiding (trans)
import Relation.Binary.NonStrictToStrict as Conv
open Conv _≈_ _≤_

strictTotalOrder : StrictTotalOrder
strictTotalOrder = record
  { isStrictTotalOrder = record
      { isEquivalence = isEquivalence
      ; trans         = trans isPartialOrder
      ; compare       = trichotomous Eq.sym _≟_ antisym total
      ; <-resp-≈      = <-resp-≈ isEquivalence ≤-resp-≈
      }
  }

open StrictTotalOrder strictTotalOrder public
