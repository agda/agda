------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by lattices
------------------------------------------------------------------------

open import Relation.Binary.Lattice

module Relation.Binary.Properties.Lattice
  {c ℓ₁ ℓ₂} (L : Lattice c ℓ₁ ℓ₂) where

open Lattice L

import Algebra as Alg
import Algebra.Structures as AlgS
import Algebra.FunctionProperties as P; open P _≈_
open import Data.Product using (_,_)
open import Function using (flip)
open import Relation.Binary
open import Relation.Binary.Properties.Poset poset
import Relation.Binary.Properties.JoinSemilattice joinSemilattice as J
import Relation.Binary.Properties.MeetSemilattice meetSemilattice as M

∨-absorbs-∧ : _∨_ Absorbs _∧_
∨-absorbs-∧ x y =
  let x≤x∨[x∧y] , _ , least = supremum  x (x ∧ y)
      x∧y≤x     , _ , _     = infimum x y
  in antisym (least x refl x∧y≤x) x≤x∨[x∧y]

∧-absorbs-∨ : _∧_ Absorbs _∨_
∧-absorbs-∨ x y =
  let x∧[x∨y]≤x , _ , greatest = infimum  x (x ∨ y)
      x≤x∨y     , _ , _        = supremum x y
  in antisym x∧[x∨y]≤x (greatest x refl x≤x∨y)

absorptive : Absorptive _∨_ _∧_
absorptive = ∨-absorbs-∧ , ∧-absorbs-∨

-- The dual construction is also a lattice.

∧-∨-isLattice : IsLattice _≈_ (flip _≤_) _∧_ _∨_
∧-∨-isLattice = record
  { isPartialOrder = invIsPartialOrder
  ; supremum       = infimum
  ; infimum        = supremum
  }

∧-∨-lattice : Lattice c ℓ₁ ℓ₂
∧-∨-lattice = record
  { _∧_       = _∨_
  ; _∨_       = _∧_
  ; isLattice = ∧-∨-isLattice
  }

-- Every order-theoretic lattice can be turned into an algebraic one.

isAlgLattice : AlgS.IsLattice _≈_ _∨_ _∧_
isAlgLattice = record
  { isEquivalence = isEquivalence
  ; ∨-comm        = J.∨-comm
  ; ∨-assoc       = J.∨-assoc
  ; ∨-cong        = J.∨-cong
  ; ∧-comm        = M.∧-comm
  ; ∧-assoc       = M.∧-assoc
  ; ∧-cong        = M.∧-cong
  ; absorptive    = absorptive
  }

algLattice : Alg.Lattice c ℓ₁
algLattice = record { isLattice = isAlgLattice }
