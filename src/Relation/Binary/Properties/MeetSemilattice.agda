------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by meet semilattices
------------------------------------------------------------------------

open import Relation.Binary.Lattice

module Relation.Binary.Properties.MeetSemilattice
  {c ℓ₁ ℓ₂} (M : MeetSemilattice c ℓ₁ ℓ₂) where

open MeetSemilattice M

import Algebra.FunctionProperties as P; open P _≈_
open import Data.Product
open import Function using (flip)
open import Relation.Binary
open import Relation.Binary.Properties.Poset poset
import Relation.Binary.Properties.JoinSemilattice as J

-- The dual construction is a join semilattice.

dualIsJoinSemilattice : IsJoinSemilattice _≈_ (flip _≤_) _∧_
dualIsJoinSemilattice = record
  { isPartialOrder = invIsPartialOrder
  ; supremum       = infimum
  }

dualJoinSemilattice : JoinSemilattice c ℓ₁ ℓ₂
dualJoinSemilattice = record
  { _∨_               = _∧_
  ; isJoinSemilattice = dualIsJoinSemilattice
  }

open J dualJoinSemilattice public renaming
  ( ∨-monotonic  to ∧-monotonic
  ; ∨-cong       to ∧-cong
  ; ∨-comm       to ∧-comm
  ; ∨-assoc      to ∧-assoc
  ; ∨-idempotent to ∧-idempotent
  )

