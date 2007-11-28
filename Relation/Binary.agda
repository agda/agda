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
  isEquivalence : IsEquivalence _≈_
  refl          : Reflexive _≈_ _∼_
  trans         : Transitive _∼_
  ≈-resp-∼      : _≈_ Respects₂ _∼_

module IsPreorderOps {a : Set} {_≈_ _∼_ : Rel a}
                     (p : IsPreorder _≈_ _∼_) where
  private
    module IP = IsPreorder p
    open IP public
  module Eq = IsEquivalence IP.isEquivalence

record Preorder : Set1 where
  carrier       : Set
  underlyingEq  : Rel carrier  -- The underlying equality.
  rel           : Rel carrier  -- The relation.
  isPreorder    : IsPreorder underlyingEq rel

module PreorderOps (p : Preorder) where
  private
    module P = Preorder p
    open P public using (carrier; isPreorder)
    open module IP = IsPreorderOps P.isPreorder public

  _≈_ : Rel carrier
  _≈_ = P.underlyingEq

  _∼_ : Rel carrier
  _∼_ = P.rel

------------------------------------------------------------------------
-- Setoids

-- Equivalence relations are defined in Relation.Binary.Core.

record Setoid : Set1 where
  carrier       : Set
  eq            : Rel carrier
  isEquivalence : IsEquivalence eq

module SetoidOps (s : Setoid) where
  private
    module S = Setoid s
    open S public using (carrier; isEquivalence)
    open module IE = IsEquivalence S.isEquivalence public

  _≈_ : Rel carrier
  _≈_ = S.eq

  preorder : Preorder
  preorder = record
    { carrier      = carrier
    ; underlyingEq = _≡_
    ; rel          = _≈_
    ; isPreorder   = record
      { isEquivalence = ≡-isEquivalence
      ; refl          = refl
      ; trans         = trans
      ; ≈-resp-∼      = ≡-resp _≈_
      }
    }

------------------------------------------------------------------------
-- Decidable equivalence relations

record IsDecEquivalence {a : Set} (_≈_ : Rel a) : Set where
  isEquivalence : IsEquivalence _≈_
  decidable     : Decidable _≈_

module IsDecEquivalenceOps {a : Set} {_≈_ : Rel a}
                           (de : IsDecEquivalence _≈_) where
  private
    module IDE = IsDecEquivalence de
    open IDE public using (isEquivalence)
    open module IE = IsEquivalence IDE.isEquivalence public

  _≟_ : Decidable _≈_
  _≟_ = IDE.decidable

record DecSetoid : Set1 where
  carrier          : Set
  eq               : Rel carrier
  isDecEquivalence : IsDecEquivalence eq

module DecSetoidOps (ds : DecSetoid) where
  private
    module DS = DecSetoid ds
    open DS public using (carrier; isDecEquivalence)
    open module IDE = IsDecEquivalenceOps DS.isDecEquivalence public

  _≈_ : Rel carrier
  _≈_ = DS.eq

  setoid : Setoid
  setoid = record
    { carrier       = carrier
    ; eq            = _≈_
    ; isEquivalence = isEquivalence
    }

------------------------------------------------------------------------
-- Partial orders

record IsPartialOrder {a : Set} (_≈_ _≤_ : Rel a) : Set where
  isPreorder    : IsPreorder _≈_ _≤_
  antisym       : Antisymmetric _≈_ _≤_

module IsPartialOrderOps {a : Set} {_≈_ _≤_ : Rel a}
                         (po : IsPartialOrder _≈_ _≤_) where
  private
    module IPO = IsPartialOrder po
    open IPO public
    open module IP = IsPreorderOps IPO.isPreorder public
           renaming (≈-resp-∼ to ≈-resp-≤)

record Poset : Set1 where
  carrier        : Set
  underlyingEq   : Rel carrier
  order          : Rel carrier
  isPartialOrder : IsPartialOrder underlyingEq order

module PosetOps (p : Poset) where
  private
    module P = Poset p
    open P public using (carrier; isPartialOrder)
    open module IPO = IsPartialOrderOps P.isPartialOrder public

  _≈_ : Rel carrier
  _≈_ = P.underlyingEq

  _≤_ : Rel carrier
  _≤_ = P.order

  -- TODO: One could add more conversions like this one.

  preorder : Preorder
  preorder = record
    { carrier      = carrier
    ; underlyingEq = _≈_
    ; rel          = _≤_
    ; isPreorder   = isPreorder
    }

------------------------------------------------------------------------
-- Strict partial orders

record IsStrictPartialOrder {a : Set} (_≈_ _<_ : Rel a) : Set where
  isEquivalence : IsEquivalence _≈_
  irrefl        : Irreflexive _≈_ _<_
  trans         : Transitive _<_
  ≈-resp-<      : _≈_ Respects₂ _<_

module IsStrictPartialOrderOps
         {a : Set} {_≈_ _≤_ : Rel a}
         (spo : IsStrictPartialOrder _≈_ _≤_) where
  private
    module ISPO = IsStrictPartialOrder spo
    open ISPO public
  module Eq = IsEquivalence ISPO.isEquivalence public

record StrictPartialOrder : Set1 where
  carrier              : Set
  underlyingEq         : Rel carrier
  order                : Rel carrier
  isStrictPartialOrder : IsStrictPartialOrder underlyingEq order

module StrictPartialOrderOps (spo : StrictPartialOrder) where
  private
    module SPO = StrictPartialOrder spo
    open SPO public using (carrier; isStrictPartialOrder)
    open module ISPO = IsStrictPartialOrderOps SPO.isStrictPartialOrder
                       public

  _≈_ : Rel carrier
  _≈_ = SPO.underlyingEq

  _<_ : Rel carrier
  _<_ = SPO.order

------------------------------------------------------------------------
-- Total orders

record IsTotalOrder {a : Set} (_≈_ _≤_ : Rel a) : Set where
  isPartialOrder : IsPartialOrder _≈_ _≤_
  total          : Total _≤_

module IsTotalOrderOps {a : Set} {_≈_ _≤_ : Rel a}
                       (to : IsTotalOrder _≈_ _≤_) where
  private
    module ITO = IsTotalOrder to
    open ITO public
    open module IPO = IsPartialOrderOps ITO.isPartialOrder public

record TotalOrder : Set1 where
  carrier      : Set
  underlyingEq : Rel carrier
  order        : Rel carrier
  isTotalOrder : IsTotalOrder underlyingEq order

module TotalOrderOps (p : TotalOrder) where
  private
    module TO = TotalOrder p
    open TO public using (carrier; isTotalOrder)
    open module ITO = IsTotalOrderOps TO.isTotalOrder public

  _≈_ : Rel carrier
  _≈_ = TO.underlyingEq

  _≤_ : Rel carrier
  _≤_ = TO.order

------------------------------------------------------------------------
-- Decidable total orders

record IsDecTotalOrder {a : Set} (_≈_ _≤_ : Rel a) : Set where
  isTotalOrder : IsTotalOrder _≈_ _≤_
  ≈-decidable  : Decidable _≈_
  ≤-decidable  : Decidable _≤_

module IsDecTotalOrderOps {a : Set} {_≈_ _≤_ : Rel a}
                          (dto : IsDecTotalOrder _≈_ _≤_) where
  private
    module IDTO = IsDecTotalOrder dto
    open IDTO public using (isTotalOrder)
    open module ITO = IsTotalOrderOps IDTO.isTotalOrder public

  _≟_ : Decidable _≈_
  _≟_ = IDTO.≈-decidable

  _≤?_ : Decidable _≤_
  _≤?_ = IDTO.≤-decidable

record DecTotalOrder : Set1 where
  carrier         : Set
  underlyingEq    : Rel carrier
  order           : Rel carrier
  isDecTotalOrder : IsDecTotalOrder underlyingEq order

module DecTotalOrderOps (p : DecTotalOrder) where
  private
    module DTO = DecTotalOrder p
    open DTO public using (carrier; isDecTotalOrder)
    open module ITO = IsDecTotalOrderOps DTO.isDecTotalOrder public

  _≈_ : Rel carrier
  _≈_ = DTO.underlyingEq

  _≤_ : Rel carrier
  _≤_ = DTO.order

  poset : Poset
  poset = record
    { carrier        = carrier
    ; underlyingEq   = _≈_
    ; order          = _≤_
    ; isPartialOrder = isPartialOrder
    }

  decSetoid : DecSetoid
  decSetoid = record
    { carrier          = carrier
    ; eq               = _≈_
    ; isDecEquivalence = record
        { isEquivalence = isEquivalence
        ; decidable     = _≟_
        }
    }
