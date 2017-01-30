------------------------------------------------------------------------
-- The Agda standard library
--
-- Order-theoretic lattices
------------------------------------------------------------------------

module Relation.Binary.Lattice where

open import Algebra.FunctionProperties
open import Data.Product
open import Function using (flip)
open import Level
open import Relation.Binary
import Relation.Binary.PropositionalEquality as PropEq

------------------------------------------------------------------------
-- Bounds and extrema

Supremum : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Op₂ A → Set _
Supremum _≤_ _∨_ =
  ∀ x y → x ≤ (x ∨ y) × y ≤ (x ∨ y) × ∀ z → x ≤ z → y ≤ z → (x ∨ y) ≤ z

Infimum : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Op₂ A → Set _
Infimum _≤_ = Supremum (flip _≤_)

Maximum : ∀ {a ℓ} {A : Set a} → Rel A ℓ → A → Set _
Maximum _≤_ ⊤ = ∀ x → x ≤ ⊤

Minimum : ∀ {a ℓ} {A : Set a} → Rel A ℓ → A → Set _
Minimum _≤_ = Maximum (flip _≤_)


------------------------------------------------------------------------
-- Semilattices

record IsJoinSemilattice {a ℓ₁ ℓ₂} {A : Set a}
                         (_≈_ : Rel A ℓ₁) -- The underlying equality.
                         (_≤_ : Rel A ℓ₂) -- The partial order.
                         (_∨_ : Op₂ A)    -- The join operation.
                         : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPartialOrder : IsPartialOrder _≈_ _≤_
    supremum       : Supremum _≤_ _∨_

  open IsPartialOrder isPartialOrder public

record JoinSemilattice c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixr 6 _∨_
  field
    Carrier           : Set c
    _≈_               : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_               : Rel Carrier ℓ₂  -- The partial order.
    _∨_               : Op₂ Carrier     -- The join operation.
    isJoinSemilattice : IsJoinSemilattice _≈_ _≤_ _∨_

  open IsJoinSemilattice isJoinSemilattice public

  poset : Poset c ℓ₁ ℓ₂
  poset = record { isPartialOrder = isPartialOrder }

  open Poset poset public using (preorder)

record IsMeetSemilattice {a ℓ₁ ℓ₂} {A : Set a}
                         (_≈_ : Rel A ℓ₁) -- The underlying equality.
                         (_≤_ : Rel A ℓ₂) -- The partial order.
                         (_∧_ : Op₂ A)    -- The meet operation.
                         : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPartialOrder : IsPartialOrder _≈_ _≤_
    infimum        : Infimum _≤_ _∧_

  open IsPartialOrder isPartialOrder public

record MeetSemilattice c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixr 7 _∧_
  field
    Carrier           : Set c
    _≈_               : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_               : Rel Carrier ℓ₂  -- The partial order.
    _∧_               : Op₂ Carrier     -- The meet operation.
    isMeetSemilattice : IsMeetSemilattice _≈_ _≤_ _∧_

  open IsMeetSemilattice isMeetSemilattice public

  poset : Poset c ℓ₁ ℓ₂
  poset = record { isPartialOrder = isPartialOrder }

  open Poset poset public using (preorder)

record IsBoundedJoinSemilattice {a ℓ₁ ℓ₂} {A : Set a}
                                (_≈_ : Rel A ℓ₁) -- The underlying equality.
                                (_≤_ : Rel A ℓ₂) -- The partial order.
                                (_∨_ : Op₂ A)    -- The join operation.
                                (⊥   : A)        -- The minimum.
                                : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isJoinSemilattice : IsJoinSemilattice _≈_ _≤_ _∨_
    minimum           : Minimum _≤_ ⊥

  open IsJoinSemilattice isJoinSemilattice public

record BoundedJoinSemilattice c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixr 6 _∨_
  field
    Carrier                  : Set c
    _≈_                      : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_                      : Rel Carrier ℓ₂  -- The partial order.
    _∨_                      : Op₂ Carrier     -- The join operation.
    ⊥                        : Carrier         -- The minimum.
    isBoundedJoinSemilattice : IsBoundedJoinSemilattice _≈_ _≤_ _∨_ ⊥

  open IsBoundedJoinSemilattice isBoundedJoinSemilattice public

  joinSemiLattice : JoinSemilattice c ℓ₁ ℓ₂
  joinSemiLattice = record { isJoinSemilattice = isJoinSemilattice }

  open JoinSemilattice joinSemiLattice public using (preorder; poset)

record IsBoundedMeetSemilattice {a ℓ₁ ℓ₂} {A : Set a}
                                (_≈_ : Rel A ℓ₁) -- The underlying equality.
                                (_≤_ : Rel A ℓ₂) -- The partial order.
                                (_∧_ : Op₂ A)    -- The join operation.
                                (⊤   : A)        -- The maximum.
                                : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isMeetSemilattice : IsMeetSemilattice _≈_ _≤_ _∧_
    maximum           : Maximum _≤_ ⊤

  open IsMeetSemilattice isMeetSemilattice public

record BoundedMeetSemilattice c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixr 7 _∧_
  field
    Carrier                  : Set c
    _≈_                      : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_                      : Rel Carrier ℓ₂  -- The partial order.
    _∧_                      : Op₂ Carrier     -- The join operation.
    ⊤                        : Carrier         -- The maximum.
    isBoundedMeetSemilattice : IsBoundedMeetSemilattice _≈_ _≤_ _∧_ ⊤

  open IsBoundedMeetSemilattice isBoundedMeetSemilattice public

  meetSemiLattice : MeetSemilattice c ℓ₁ ℓ₂
  meetSemiLattice = record { isMeetSemilattice = isMeetSemilattice }

  open MeetSemilattice meetSemiLattice public using (preorder; poset)

------------------------------------------------------------------------
-- Lattices

record IsLattice {a ℓ₁ ℓ₂} {A : Set a}
                 (_≈_ : Rel A ℓ₁) -- The underlying equality.
                 (_≤_ : Rel A ℓ₂) -- The partial order.
                 (_∨_ : Op₂ A)    -- The join operation.
                 (_∧_ : Op₂ A)    -- The meet operation.
                 : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPartialOrder : IsPartialOrder _≈_ _≤_
    supremum       : Supremum _≤_ _∨_
    infimum        : Infimum _≤_ _∧_

  isJoinSemilattice : IsJoinSemilattice _≈_ _≤_ _∨_
  isJoinSemilattice = record
    { isPartialOrder = isPartialOrder
    ; supremum       = supremum
    }

  isMeetSemilattice : IsMeetSemilattice _≈_ _≤_ _∧_
  isMeetSemilattice = record
    { isPartialOrder = isPartialOrder
    ; infimum        = infimum
    }

  open IsPartialOrder isPartialOrder public

record Lattice c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixr 6 _∨_
  infixr 7 _∧_
  field
    Carrier   : Set c
    _≈_       : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_       : Rel Carrier ℓ₂  -- The partial order.
    _∨_       : Op₂ Carrier     -- The join operation.
    _∧_       : Op₂ Carrier     -- The meet operation.
    isLattice : IsLattice _≈_ _≤_ _∨_ _∧_

  open IsLattice isLattice public

  joinSemilattice : JoinSemilattice c ℓ₁ ℓ₂
  joinSemilattice = record { isJoinSemilattice = isJoinSemilattice }

  meetSemilattice : MeetSemilattice c ℓ₁ ℓ₂
  meetSemilattice = record { isMeetSemilattice = isMeetSemilattice }

  open JoinSemilattice joinSemilattice public using (poset; preorder)

record IsBoundedLattice {a ℓ₁ ℓ₂} {A : Set a}
                        (_≈_ : Rel A ℓ₁) -- The underlying equality.
                        (_≤_ : Rel A ℓ₂) -- The partial order.
                        (_∨_ : Op₂ A)    -- The join operation.
                        (_∧_ : Op₂ A)    -- The meet operation.
                        (⊤   : A)        -- The maximum.
                        (⊥   : A)        -- The minimum.
                        : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isLattice : IsLattice _≈_ _≤_ _∨_ _∧_
    maximum   : Maximum _≤_ ⊤
    minimum   : Minimum _≤_ ⊥

  open IsLattice isLattice public

  isBoundedJoinSemilattice : IsBoundedJoinSemilattice _≈_ _≤_ _∨_ ⊥
  isBoundedJoinSemilattice = record
    { isJoinSemilattice = isJoinSemilattice
    ; minimum           = minimum
    }

  isBoundedMeetSemilattice : IsBoundedMeetSemilattice _≈_ _≤_ _∧_ ⊤
  isBoundedMeetSemilattice = record
    { isMeetSemilattice = isMeetSemilattice
    ; maximum           = maximum
    }

record BoundedLattice c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixr 6 _∨_
  infixr 7 _∧_
  field
    Carrier          : Set c
    _≈_              : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_              : Rel Carrier ℓ₂  -- The partial order.
    _∨_              : Op₂ Carrier     -- The join operation.
    _∧_              : Op₂ Carrier     -- The meet operation.
    ⊤                : Carrier         -- The maximum.
    ⊥                : Carrier         -- The minimum.
    isBoundedLattice : IsBoundedLattice _≈_ _≤_ _∨_ _∧_ ⊤ ⊥

  open IsBoundedLattice isBoundedLattice public

  boundedJoinSemilattice : BoundedJoinSemilattice c ℓ₁ ℓ₂
  boundedJoinSemilattice = record
    { isBoundedJoinSemilattice = isBoundedJoinSemilattice }

  boundedMeetSemilattice : BoundedMeetSemilattice c ℓ₁ ℓ₂
  boundedMeetSemilattice = record
    { isBoundedMeetSemilattice = isBoundedMeetSemilattice }
