------------------------------------------------------------------------
-- Divisibility and coprimality
------------------------------------------------------------------------

module Data.Integer.Divisibility where

open import Data.Function
open import Data.Integer
open import Data.Integer.Properties
import Data.Nat.Divisibility as ℕ
import Data.Nat.Coprimality as ℕ
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

-- Divisibility.

infix 4 _∣_

_∣_ : Rel ℤ
_∣_ = ℕ._∣_ on₁ ∣_∣

-- Coprimality.

Coprime : Rel ℤ
Coprime = ℕ.Coprime on₁ ∣_∣

-- If i divides jk and is coprime to j, then it divides k.

coprime-divisor : ∀ i j k → Coprime i j → i ∣ j * k → i ∣ k
coprime-divisor i j k c eq =
  ℕ.coprime-divisor c (subst (ℕ._∣_ ∣ i ∣) (abs-*-commute j k) eq)
