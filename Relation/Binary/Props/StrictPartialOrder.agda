------------------------------------------------------------------------
-- Properties satisfied by strict partial orders
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Props.StrictPartialOrder
       (spo : StrictPartialOrder)
       where

open Relation.Binary.StrictPartialOrder spo
import Relation.Binary.StrictToNonStrict as Conv
open Conv _≈_ _<_

------------------------------------------------------------------------
-- Strict partial orders can be converted to posets

poset : Poset
poset = record
  { carrier        = carrier
  ; _≈_            = _≈_
  ; _≤_            = _≤_
  ; isPartialOrder = record
    { isPreorder = record
        { isEquivalence = isEquivalence
        ; refl     = ≤-refl
        ; trans    = ≤-trans isEquivalence ≈-resp-< trans
        ; ≈-resp-∼ = ≈-resp-≤ isEquivalence ≈-resp-<
        }
    ; antisym = ≤-antisym isEquivalence trans irrefl
    }
  }

open Poset poset public
