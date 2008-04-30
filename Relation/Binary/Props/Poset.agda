------------------------------------------------------------------------
-- Properties satisfied by posets
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Props.Poset (p : Poset) where

open Relation.Binary.Poset p
import Relation.Binary.NonStrictToStrict as Conv
open Conv _≈_ _≤_

------------------------------------------------------------------------
-- Posets can be turned into strict partial orders

strictPartialOrder : StrictPartialOrder
strictPartialOrder = record
  { carrier              = carrier
  ; _≈_                  = _≈_
  ; _<_                  = _<_
  ; isStrictPartialOrder = record
    { isEquivalence = isEquivalence
    ; irrefl        = <-irrefl
    ; trans         = <-trans isPartialOrder
    ; ≈-resp-<      = ≈-resp-< isEquivalence ≈-resp-≤
    }
  }

open StrictPartialOrder strictPartialOrder
