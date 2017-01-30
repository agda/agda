------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by bounded meet semilattices
------------------------------------------------------------------------

open import Relation.Binary.Lattice

module Relation.Binary.Properties.BoundedMeetSemilattice
  {c ℓ₁ ℓ₂} (M : BoundedMeetSemilattice c ℓ₁ ℓ₂) where

open BoundedMeetSemilattice M

import Algebra.FunctionProperties as P; open P _≈_
open import Data.Product
open import Function using (_∘_; flip)
open import Relation.Binary
open import Relation.Binary.Properties.Poset poset
import Relation.Binary.Properties.BoundedJoinSemilattice as J

-- The dual construction is a bounded join semilattice.

dualIsBoundedJoinSemilattice : IsBoundedJoinSemilattice _≈_ (flip _≤_) _∧_ ⊤
dualIsBoundedJoinSemilattice = record
  { isJoinSemilattice = record
    { isPartialOrder  = invIsPartialOrder
    ; supremum        = infimum
    }
  ; minimum           = maximum
  }

dualBoundedJoinSemilattice : BoundedJoinSemilattice c ℓ₁ ℓ₂
dualBoundedJoinSemilattice = record
  { ⊥                        = ⊤
  ; isBoundedJoinSemilattice = dualIsBoundedJoinSemilattice
  }

open J dualBoundedJoinSemilattice public
