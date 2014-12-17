------------------------------------------------------------------------
-- The Agda standard library
--
-- Some unit types
------------------------------------------------------------------------

module Data.Unit where

open import Data.Sum
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

-- Some types and operations are defined in
-- Data.Unit.Core and Data.Unit.Minimal.

open import Data.Unit.Core    public
open import Data.Unit.Minimal public

------------------------------------------------------------------------
-- Operations

_≟_ : Decidable {A = ⊤} _≡_
_ ≟ _ = yes refl

_≤?_ : Decidable _≤_
_ ≤? _ = yes _

total : Total _≤_
total _ _ = inj₁ _

------------------------------------------------------------------------
-- Properties

preorder : Preorder _ _ _
preorder = PropEq.preorder ⊤

setoid : Setoid _ _
setoid = PropEq.setoid ⊤

decTotalOrder : DecTotalOrder _ _ _
decTotalOrder = record
  { Carrier         = ⊤
  ; _≈_             = _≡_
  ; _≤_             = _≤_
  ; isDecTotalOrder = record
      { isTotalOrder = record
          { isPartialOrder = record
              { isPreorder = record
                  { isEquivalence = PropEq.isEquivalence
                  ; reflexive     = λ _ → _
                  ; trans         = λ _ _ → _
                  }
              ; antisym  = antisym
              }
          ; total = total
          }
      ; _≟_  = _≟_
      ; _≤?_ = _≤?_
      }
  }
  where
  antisym : Antisymmetric _≡_ _≤_
  antisym _ _ = refl

decSetoid : DecSetoid _ _
decSetoid = DecTotalOrder.Eq.decSetoid decTotalOrder

poset : Poset _ _ _
poset = DecTotalOrder.poset decTotalOrder
