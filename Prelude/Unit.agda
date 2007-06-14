------------------------------------------------------------------------
-- The unit type
------------------------------------------------------------------------

module Prelude.Unit where

open import Prelude.Logic
open import Prelude.Sum
open import Prelude.BinaryRelation
open import Prelude.BinaryRelation.PropositionalEquality

------------------------------------------------------------------------
-- Types

data ⊤ : Set where
  tt : ⊤

record _⊤-≤_ (x y : ⊤) : Set where

------------------------------------------------------------------------
-- Operations

_⊤-≟_ : Decidable {⊤} _≡_
tt ⊤-≟ tt = yes ≡-refl

_⊤-≤?_ : Decidable _⊤-≤_
_ ⊤-≤? _ = yes _

⊤-total : Total _⊤-≤_
⊤-total _ _ = inj₁ _

------------------------------------------------------------------------
-- Properties

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
  antisym {tt} {tt} _ _ = ≡-refl

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
