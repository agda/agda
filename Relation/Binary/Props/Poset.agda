------------------------------------------------------------------------
-- Properties satisfied by posets
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Props.Poset (p : Poset) where

private
  open module P = Relation.Binary.PosetOps p
import Relation.Binary.NonStrictToStrict as Conv
private
  open module C = Conv _≈_ _≤_

------------------------------------------------------------------------
-- Posets can be turned into strict partial orders

strictPartialOrder : StrictPartialOrder
strictPartialOrder = record
  { carrier              = carrier
  ; underlyingEq         = _≈_
  ; order                = _<_
  ; isStrictPartialOrder = record
    { isEquivalence = isEquivalence
    ; irrefl        = <-irrefl
    ; trans         = <-trans isPartialOrder
    ; ≈-resp-<      = ≈-resp-< isEquivalence ≈-resp-≤
    }
  }
