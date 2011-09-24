------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by strict partial orders
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Props.StrictPartialOrder
       {s₁ s₂ s₃} (SPO : StrictPartialOrder s₁ s₂ s₃) where

open Relation.Binary.StrictPartialOrder SPO
  renaming (trans to <-trans)
import Relation.Binary.StrictToNonStrict as Conv
open Conv _≈_ _<_

------------------------------------------------------------------------
-- Strict partial orders can be converted to posets

poset : Poset _ _ _
poset = record
  { isPartialOrder = record
    { isPreorder = record
        { isEquivalence = isEquivalence
        ; reflexive     = reflexive
        ; trans         = trans isEquivalence <-resp-≈ <-trans
        }
    ; antisym = antisym isEquivalence <-trans irrefl
    }
  }

open Poset poset public
