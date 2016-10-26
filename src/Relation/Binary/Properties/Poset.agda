------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by posets
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Properties.Poset
         {p₁ p₂ p₃} (P : Poset p₁ p₂ p₃) where

open Relation.Binary.Poset P hiding (trans)
import Relation.Binary.NonStrictToStrict as Conv
open Conv _≈_ _≤_
open import Relation.Binary.Properties.Preorder preorder
open import Function using (flip)

-- The inverse relation is also a poset.

invIsPartialOrder : IsPartialOrder _≈_ (flip _≤_)
invIsPartialOrder = record
  { isPreorder   = invIsPreorder
  ; antisym      = flip antisym
  }

invPoset : Poset p₁ p₂ p₃
invPoset = record { isPartialOrder = invIsPartialOrder }

------------------------------------------------------------------------
-- Posets can be turned into strict partial orders

strictPartialOrder : StrictPartialOrder _ _ _
strictPartialOrder = record
  { isStrictPartialOrder = record
    { isEquivalence = isEquivalence
    ; irrefl        = irrefl
    ; trans         = trans isPartialOrder
    ; <-resp-≈      = <-resp-≈ isEquivalence ≤-resp-≈
    }
  }

open StrictPartialOrder strictPartialOrder
