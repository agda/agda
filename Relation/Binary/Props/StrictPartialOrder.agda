------------------------------------------------------------------------
-- Properties satisfied by strict partial orders
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Props.StrictPartialOrder
       (spo : StrictPartialOrder)
       where

private
  open module SPO = Relation.Binary.StrictPartialOrderOps spo
import Relation.Binary.StrictToNonStrict as Conv
private
  open module C = Conv _≈_ _<_

------------------------------------------------------------------------
-- Strict partial orders can be converted to posets

poset : Poset
poset = record
  { carrier        = carrier
  ; underlyingEq   = _≈_
  ; order          = _≤_
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
