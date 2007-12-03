------------------------------------------------------------------------
-- Properties of homogeneous binary relations
------------------------------------------------------------------------

module Relation.Binary where

open import Logic
open import Data.Product
open import Data.Sum
open import Data.Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Core

open import Relation.Binary.Core public

------------------------------------------------------------------------
-- Preorders

record IsPreorder {a : Set}
                  (_≈_ : Rel a) -- The underlying equality.
                  (_∼_ : Rel a) -- The relation.
                  : Set where
  field
    isEquivalence : IsEquivalence _≈_
    refl          : Reflexive _≈_ _∼_
    trans         : Transitive _∼_
    ≈-resp-∼      : _≈_ Respects₂ _∼_

  module Eq = IsEquivalence isEquivalence

record Preorder : Set1 where
  field
    carrier    : Set
    _≈_        : Rel carrier  -- The underlying equality.
    _∼_        : Rel carrier  -- The relation.
    isPreorder : IsPreorder _≈_ _∼_

  open IsPreorder isPreorder public

------------------------------------------------------------------------
-- Setoids

-- Equivalence relations are defined in Relation.Binary.Core.

record Setoid : Set1 where
  field
    carrier       : Set
    _≈_           : Rel carrier
    isEquivalence : IsEquivalence _≈_

  open IsEquivalence isEquivalence public

  -- TODO: One could add more conversions like this one.

  preorder : Preorder
  preorder = record
    { carrier    = carrier
    ; _≈_        = _≡_
    ; _∼_        = _≈_
    ; isPreorder = record
      { isEquivalence = ≡-isEquivalence
      ; refl          = refl
      ; trans         = trans
      ; ≈-resp-∼      = ≡-resp _≈_
      }
    }

------------------------------------------------------------------------
-- Decidable equivalence relations

record IsDecEquivalence {a : Set} (_≈_ : Rel a) : Set where
  field
    isEquivalence : IsEquivalence _≈_
    _≟_           : Decidable _≈_

  open IsEquivalence isEquivalence public

record DecSetoid : Set1 where
  field
    carrier          : Set
    _≈_              : Rel carrier
    isDecEquivalence : IsDecEquivalence _≈_

  open IsDecEquivalence isDecEquivalence public

  setoid : Setoid
  setoid = record
    { carrier       = carrier
    ; _≈_           = _≈_
    ; isEquivalence = isEquivalence
    }

------------------------------------------------------------------------
-- Partial orders

record IsPartialOrder {a : Set} (_≈_ _≤_ : Rel a) : Set where
  field
    isPreorder : IsPreorder _≈_ _≤_
    antisym    : Antisymmetric _≈_ _≤_

  open IsPreorder isPreorder public
         renaming (≈-resp-∼ to ≈-resp-≤)

record Poset : Set1 where
  field
    carrier        : Set
    _≈_            : Rel carrier
    _≤_            : Rel carrier
    isPartialOrder : IsPartialOrder _≈_ _≤_

  open IsPartialOrder isPartialOrder public

  preorder : Preorder
  preorder = record
    { carrier    = carrier
    ; _≈_        = _≈_
    ; _∼_        = _≤_
    ; isPreorder = isPreorder
    }

------------------------------------------------------------------------
-- Strict partial orders

record IsStrictPartialOrder {a : Set} (_≈_ _<_ : Rel a) : Set where
  field
    isEquivalence : IsEquivalence _≈_
    irrefl        : Irreflexive _≈_ _<_
    trans         : Transitive _<_
    ≈-resp-<      : _≈_ Respects₂ _<_

  module Eq = IsEquivalence isEquivalence

record StrictPartialOrder : Set1 where
  field
    carrier              : Set
    _≈_                  : Rel carrier
    _<_                  : Rel carrier
    isStrictPartialOrder : IsStrictPartialOrder _≈_ _<_

  open IsStrictPartialOrder isStrictPartialOrder public

------------------------------------------------------------------------
-- Total orders

record IsTotalOrder {a : Set} (_≈_ _≤_ : Rel a) : Set where
  field
    isPartialOrder : IsPartialOrder _≈_ _≤_
    total          : Total _≤_

  open IsPartialOrder isPartialOrder public

record TotalOrder : Set1 where
  field
    carrier      : Set
    _≈_          : Rel carrier
    _≤_          : Rel carrier
    isTotalOrder : IsTotalOrder _≈_ _≤_

  open IsTotalOrder isTotalOrder public

------------------------------------------------------------------------
-- Decidable total orders

record IsDecTotalOrder {a : Set} (_≈_ _≤_ : Rel a) : Set where
  field
    isTotalOrder : IsTotalOrder _≈_ _≤_
    _≟_          : Decidable _≈_
    _≤?_         : Decidable _≤_

  open IsTotalOrder isTotalOrder public

record DecTotalOrder : Set1 where
  field
    carrier         : Set
    _≈_             : Rel carrier
    _≤_             : Rel carrier
    isDecTotalOrder : IsDecTotalOrder _≈_ _≤_

  open IsDecTotalOrder isDecTotalOrder public

  poset : Poset
  poset = record
    { carrier        = carrier
    ; _≈_            = _≈_
    ; _≤_            = _≤_
    ; isPartialOrder = isPartialOrder
    }

  decSetoid : DecSetoid
  decSetoid = record
    { carrier          = carrier
    ; _≈_              = _≈_
    ; isDecEquivalence = record
        { isEquivalence = isEquivalence
        ; _≟_           = _≟_
        }
    }
