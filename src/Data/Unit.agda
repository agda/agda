------------------------------------------------------------------------
-- The unit type
------------------------------------------------------------------------

module Data.Unit where

open import Data.Sum
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

------------------------------------------------------------------------
-- Types

-- Note that the name of this type is "\top", not T.

record ⊤ : Set where

tt : ⊤
tt = record {}

record _≤_ (x y : ⊤) : Set where

------------------------------------------------------------------------
-- Operations

_≟_ : Decidable {⊤} _≡_
_ ≟ _ = yes refl

_≤?_ : Decidable _≤_
_ ≤? _ = yes _

total : Total _≤_
total _ _ = inj₁ _

------------------------------------------------------------------------
-- Properties

preorder : Preorder
preorder = PropEq.preorder ⊤

setoid : Setoid
setoid = PropEq.setoid ⊤

decTotalOrder : DecTotalOrder
decTotalOrder = record
  { carrier         = ⊤
  ; _≈_             = _≡_
  ; _≤_             = _≤_
  ; isDecTotalOrder = record
      { isTotalOrder = record
          { isPartialOrder = record
              { isPreorder = record
                  { isEquivalence = PropEq.isEquivalence
                  ; reflexive     = λ _ → _
                  ; trans         = λ _ _ → _
                  ; ∼-resp-≈      = PropEq.resp₂ _≤_
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

decSetoid : DecSetoid
decSetoid = DecTotalOrder.Eq.decSetoid decTotalOrder

poset : Poset
poset = DecTotalOrder.poset decTotalOrder
