------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural numbers defined in terms of Data.Star
------------------------------------------------------------------------

module Data.Star.Nat where

open import Data.Star
open import Data.Unit
open import Function
open import Relation.Binary
open import Relation.Binary.Simple

-- Natural numbers.

ℕ : Set
ℕ = Star Always tt tt

-- Zero and successor.

zero : ℕ
zero = ε

suc : ℕ → ℕ
suc = _◅_ _

-- The length of a star-list.

length : ∀ {i t} {I : Set i} {T : Rel I t} {i j} → Star T i j → ℕ
length = gmap (const _) (const _)

-- Arithmetic.

infixl 7 _*_
infixl 6 _+_ _∸_

_+_ : ℕ → ℕ → ℕ
_+_ = _◅◅_

_*_ : ℕ → ℕ → ℕ
_*_ m = const m ⋆

_∸_ : ℕ → ℕ → ℕ
m       ∸ ε       = m
ε       ∸ (_ ◅ n) = zero
(_ ◅ m) ∸ (_ ◅ n) = m ∸ n

-- Some constants.

0# = zero
1# = suc 0#
2# = suc 1#
3# = suc 2#
4# = suc 3#
5# = suc 4#
