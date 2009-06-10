------------------------------------------------------------------------
-- Properties of homogeneous binary relations
------------------------------------------------------------------------

module Relation.Binary where

open import Data.Product
open import Data.Sum
open import Data.Function
import Relation.Binary.PropositionalEquality.Core as PropEq
open import Relation.Binary.Consequences
open import Relation.Binary.Core as Core using (_≡_)

------------------------------------------------------------------------
-- Simple properties and equivalence relations

open Core public hiding (_≡_; refl; _≢_)

------------------------------------------------------------------------
-- Preorders

record IsPreorder {a : Set}
                  (_≈_ : Rel a) -- The underlying equality.
                  (_∼_ : Rel a) -- The relation.
                  : Set where
  field
    isEquivalence : IsEquivalence _≈_
    -- Reflexivity is expressed in terms of an underlying equality:
    reflexive     : _≈_ ⇒ _∼_
    trans         : Transitive _∼_
    ∼-resp-≈      : _∼_ Respects₂ _≈_

  module Eq = IsEquivalence isEquivalence

  refl : Reflexive _∼_
  refl = reflexive Eq.refl

record Preorder : Set₁ where
  infix 4 _≈_ _∼_
  field
    carrier    : Set
    _≈_        : Rel carrier  -- The underlying equality.
    _∼_        : Rel carrier  -- The relation.
    isPreorder : IsPreorder _≈_ _∼_

  open IsPreorder isPreorder public

------------------------------------------------------------------------
-- Setoids

-- Equivalence relations are defined in Relation.Binary.Core.

record Setoid : Set₁ where
  infix 4 _≈_
  field
    carrier       : Set
    _≈_           : Rel carrier
    isEquivalence : IsEquivalence _≈_

  open IsEquivalence isEquivalence public

  isPreorder : IsPreorder _≡_ _≈_
  isPreorder = record
    { isEquivalence = PropEq.isEquivalence
    ; reflexive     = reflexive
    ; trans         = trans
    ; ∼-resp-≈      = PropEq.resp₂ _≈_
    }

  preorder : Preorder
  preorder = record { isPreorder = isPreorder }

------------------------------------------------------------------------
-- Decidable equivalence relations

record IsDecEquivalence {a : Set} (_≈_ : Rel a) : Set where
  field
    isEquivalence : IsEquivalence _≈_
    _≟_           : Decidable _≈_

  open IsEquivalence isEquivalence public

record DecSetoid : Set₁ where
  infix 4 _≈_
  field
    carrier          : Set
    _≈_              : Rel carrier
    isDecEquivalence : IsDecEquivalence _≈_

  open IsDecEquivalence isDecEquivalence public

  setoid : Setoid
  setoid = record { isEquivalence = isEquivalence }

  open Setoid setoid public using (preorder)

------------------------------------------------------------------------
-- Partial orders

record IsPartialOrder {a : Set} (_≈_ _≤_ : Rel a) : Set where
  field
    isPreorder : IsPreorder _≈_ _≤_
    antisym    : Antisymmetric _≈_ _≤_

  open IsPreorder isPreorder public
         renaming (∼-resp-≈ to ≤-resp-≈)

record Poset : Set₁ where
  infix 4 _≈_ _≤_
  field
    carrier        : Set
    _≈_            : Rel carrier
    _≤_            : Rel carrier
    isPartialOrder : IsPartialOrder _≈_ _≤_

  open IsPartialOrder isPartialOrder public

  preorder : Preorder
  preorder = record { isPreorder = isPreorder }

------------------------------------------------------------------------
-- Strict partial orders

record IsStrictPartialOrder {a : Set} (_≈_ _<_ : Rel a) : Set where
  field
    isEquivalence : IsEquivalence _≈_
    irrefl        : Irreflexive _≈_ _<_
    trans         : Transitive _<_
    <-resp-≈      : _<_ Respects₂ _≈_

  module Eq = IsEquivalence isEquivalence

record StrictPartialOrder : Set₁ where
  infix 4 _≈_ _<_
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

record TotalOrder : Set₁ where
  infix 4 _≈_ _≤_
  field
    carrier      : Set
    _≈_          : Rel carrier
    _≤_          : Rel carrier
    isTotalOrder : IsTotalOrder _≈_ _≤_

  open IsTotalOrder isTotalOrder public

  poset : Poset
  poset = record { isPartialOrder = isPartialOrder }

  open Poset poset public using (preorder)

------------------------------------------------------------------------
-- Decidable total orders

record IsDecTotalOrder {a : Set} (_≈_ _≤_ : Rel a) : Set where
  field
    isTotalOrder : IsTotalOrder _≈_ _≤_
    _≟_          : Decidable _≈_
    _≤?_         : Decidable _≤_

  private
    module TO = IsTotalOrder isTotalOrder
  open TO public hiding (module Eq)

  module Eq where

    isDecEquivalence : IsDecEquivalence _≈_
    isDecEquivalence = record
      { isEquivalence = TO.isEquivalence
      ; _≟_           = _≟_
      }

    open IsDecEquivalence isDecEquivalence public

record DecTotalOrder : Set₁ where
  infix 4 _≈_ _≤_
  field
    carrier         : Set
    _≈_             : Rel carrier
    _≤_             : Rel carrier
    isDecTotalOrder : IsDecTotalOrder _≈_ _≤_

  private
    module DTO = IsDecTotalOrder isDecTotalOrder
  open DTO public hiding (module Eq)

  totalOrder : TotalOrder
  totalOrder = record { isTotalOrder = isTotalOrder }

  open TotalOrder totalOrder public using (poset; preorder)

  module Eq where

    decSetoid : DecSetoid
    decSetoid = record { isDecEquivalence = DTO.Eq.isDecEquivalence }

    open DecSetoid decSetoid public

------------------------------------------------------------------------
-- Strict total orders

-- Note that these orders are decidable (see compare).

record IsStrictTotalOrder {a : Set} (_≈_ _<_ : Rel a) : Set where
  field
    isEquivalence : IsEquivalence _≈_
    trans         : Transitive _<_
    compare       : Trichotomous _≈_ _<_
    <-resp-≈      : _<_ Respects₂ _≈_

  _≟_ : Decidable _≈_
  _≟_ = tri⟶dec≈ compare

  isDecEquivalence : IsDecEquivalence _≈_
  isDecEquivalence = record
    { isEquivalence = isEquivalence
    ; _≟_           = _≟_
    }

  module Eq = IsDecEquivalence isDecEquivalence

  isStrictPartialOrder : IsStrictPartialOrder _≈_ _<_
  isStrictPartialOrder = record
    { isEquivalence = isEquivalence
    ; irrefl        = tri⟶irr <-resp-≈ Eq.sym compare
    ; trans         = trans
    ; <-resp-≈      = <-resp-≈
    }

  open IsStrictPartialOrder isStrictPartialOrder using (irrefl)

record StrictTotalOrder : Set₁ where
  infix 4 _≈_ _<_
  field
    carrier            : Set
    _≈_                : Rel carrier
    _<_                : Rel carrier
    isStrictTotalOrder : IsStrictTotalOrder _≈_ _<_

  open IsStrictTotalOrder isStrictTotalOrder public
    hiding (module Eq)

  strictPartialOrder : StrictPartialOrder
  strictPartialOrder =
    record { isStrictPartialOrder = isStrictPartialOrder }

  decSetoid : DecSetoid
  decSetoid = record { isDecEquivalence = isDecEquivalence }

  module Eq = DecSetoid decSetoid
