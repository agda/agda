------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by bounded join semilattices
------------------------------------------------------------------------

open import Relation.Binary.Lattice

module Relation.Binary.Properties.BoundedJoinSemilattice
  {c ℓ₁ ℓ₂} (J : BoundedJoinSemilattice c ℓ₁ ℓ₂) where

open BoundedJoinSemilattice J

import Algebra.FunctionProperties as P; open P _≈_
open import Data.Product
open import Function using (_∘_; flip)
open import Relation.Binary
open import Relation.Binary.Properties.Poset poset

-- Bottom is an identity of the meet operation.

identityˡ : LeftIdentity ⊥ _∨_
identityˡ x =
  let _ , x≤⊥∨x , least = supremum ⊥ x
  in antisym (least x (minimum x) refl) x≤⊥∨x

identityʳ : RightIdentity ⊥ _∨_
identityʳ x =
  let x≤x∨⊥ , _ , least = supremum x ⊥
  in antisym (least x refl (minimum x)) x≤x∨⊥

identity : Identity ⊥ _∨_
identity = identityˡ , identityʳ


-- The dual construction is a bounded meet semilattice.

dualIsBoundedMeetSemilattice : IsBoundedMeetSemilattice _≈_ (flip _≤_) _∨_ ⊥
dualIsBoundedMeetSemilattice = record
  { isMeetSemilattice = record
    { isPartialOrder  = invIsPartialOrder
    ; infimum         = supremum
    }
  ; maximum           = minimum
  }

dualBoundedMeetSemilattice : BoundedMeetSemilattice c ℓ₁ ℓ₂
dualBoundedMeetSemilattice = record
  { ⊤                        = ⊥
  ; isBoundedMeetSemilattice = dualIsBoundedMeetSemilattice
  }
