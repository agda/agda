------------------------------------------------------------------------
-- The unit type
------------------------------------------------------------------------

module Data.Unit where

open import Logic
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Types

record ⊤ : Set where

tt : ⊤
tt = record {}

record _⊤-≤_ (x y : ⊤) : Set where

------------------------------------------------------------------------
-- Operations

_⊤-≟_ : Decidable {⊤} _≡_
_ ⊤-≟ _ = yes ≡-refl

_⊤-≤?_ : Decidable _⊤-≤_
_ ⊤-≤? _ = yes _

⊤-total : Total _⊤-≤_
⊤-total _ _ = inj₁ _

------------------------------------------------------------------------
-- Properties

⊤-preSetoid : PreSetoid
⊤-preSetoid = ≡-preSetoid ⊤

⊤-setoid : Setoid
⊤-setoid = ≡-setoid ⊤

⊤-decSetoid : DecSetoid
⊤-decSetoid = record { setoid = ⊤-setoid; _≟_ = _⊤-≟_ }

⊤-partialOrder : PartialOrder _≡_ _⊤-≤_
⊤-partialOrder = record
  { equiv    = ≡-equivalence
  ; preorder = record
      { refl    = \_ -> _
      ; trans   = \_ _ -> _
      }
  ; antisym  = antisym
  ; ≈-resp-≤ = subst⟶resp₂ _⊤-≤_ ≡-subst
  }
  where
  antisym : Antisymmetric _≡_ _⊤-≤_
  antisym _ _ = ≡-refl

⊤-poset : Poset
⊤-poset = record
  { carrier  = ⊤
  ; _≈_      = _≡_
  ; _≤_      = _⊤-≤_
  ; ord      = ⊤-partialOrder
  }

⊤-decTotOrder : DecTotOrder
⊤-decTotOrder = record
  { poset = ⊤-poset
  ; _≟_   = _⊤-≟_
  ; _≤?_  = _⊤-≤?_
  ; total = ⊤-total
  }
