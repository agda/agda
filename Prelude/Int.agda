------------------------------------------------------------------------
-- Integers
------------------------------------------------------------------------

module Prelude.Int where

open import Prelude.Bool
import Prelude.Nat as N
open N using (ℕ)
open import Prelude.Logic
open import Prelude.BinaryRelation
open import Prelude.BinaryRelation.PropositionalEquality
open import Prelude.Algebra
open import Prelude.Algebraoid
import Prelude.RingSolver
import Prelude.Algebra.CommutativeRingProperties as CRProp

infix  8 +_ -_
infixl 7 _*_ _⊓_
infixl 6 _+_ _-_ _⊔_

------------------------------------------------------------------------
-- The types

postulate
  ℤ   : Set
  _≤_ : ℤ -> ℤ -> Set

{-# BUILTIN INTEGER ℤ #-}

------------------------------------------------------------------------
-- Arithmetic

private
  postulate Float : Set

  {-# BUILTIN FLOAT Float #-}

  primitive
    primIntegerPlus   : ℤ -> ℤ -> ℤ
    primIntegerMinus  : ℤ -> ℤ -> ℤ
    primIntegerTimes  : ℤ -> ℤ -> ℤ
    primIntegerLess   : ℤ -> ℤ -> Bool
    primIntegerEquals : ℤ -> ℤ -> Bool
    primRound         : Float -> ℤ

_+_ : ℤ -> ℤ -> ℤ
_+_ = primIntegerPlus

_-_ : ℤ -> ℤ -> ℤ
_-_ = primIntegerMinus

_*_ : ℤ -> ℤ -> ℤ
_*_ = primIntegerTimes

0# : ℤ
0# = primRound 0.0

1# : ℤ
1# = primRound 1.0

suc : ℤ -> ℤ
suc i = i + 1#

pred : ℤ -> ℤ
pred i = i - 1#

+_ : ℕ -> ℤ
+ N.zero  = 0#
+ N.suc n = suc (+ n)

-_ : ℤ -> ℤ
- i = 0# - i

_⊔_ : ℤ -> ℤ -> ℤ
i ⊔ j = if primIntegerLess i j then i else j

_⊓_ : ℤ -> ℤ -> ℤ
i ⊓ j = if primIntegerLess i j then j else i

------------------------------------------------------------------------
-- Queries

_≟_ : Decidable {ℤ} _≡_
i ≟ j with primIntegerEquals i j
i ≟ j | true  = yes trustMe
  where postulate trustMe : _
i ≟ j | false = no trustMe
  where postulate trustMe : _

_≤?_ : Decidable {ℤ} _≤_
i ≤? j with primIntegerLess j i
i ≤? j | false = yes trustMe
  where postulate trustMe : _
i ≤? j | true  = no trustMe
  where postulate trustMe : _

------------------------------------------------------------------------
-- Some properties

ℤ-setoid : Setoid
ℤ-setoid = ≡-setoid ℤ

ℤ-decSetoid : DecSetoid
ℤ-decSetoid = record { setoid = ℤ-setoid; _≟_ = _≟_ }

ℤ-poset : Poset
ℤ-poset = record
  { carrier  = ℤ
  ; _≈_      = _≡_
  ; _≤_      = _≤_
  ; ord      = trustMe
  }
  where postulate trustMe : _

ℤ-decTotOrder : DecTotOrder
ℤ-decTotOrder = record
  { poset = ℤ-poset
  ; _≟_   = _≟_
  ; _≤?_  = _≤?_
  ; total = trustMe
  }
  where postulate trustMe : _

ℤ-commRingoid : CommutativeRingoid
ℤ-commRingoid = record
  { setoid   = ℤ-setoid
  ; _+_      = _+_
  ; _*_      = _*_
  ; -_       = -_
  ; 0#       = 0#
  ; 1#       = 1#
  ; commRing = trustMe
  }
  where postulate trustMe : _

module ℤ-ringSolver =
  Prelude.RingSolver (CRProp.almostCommRingoid ℤ-commRingoid)
