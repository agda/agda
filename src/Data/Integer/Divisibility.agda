------------------------------------------------------------------------
-- The Agda standard library
--
-- Divisibility and coprimality
------------------------------------------------------------------------

module Data.Integer.Divisibility where

open import Function
open import Data.Integer
open import Data.Integer.Properties
import Data.Nat.Divisibility as ℕ
import Data.Nat.Coprimality as ℕ
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

-- Divisibility.

infix 4 _∣_

_∣_ : Rel ℤ zero
_∣_ = ℕ._∣_ on ∣_∣

-- Coprimality.

Coprime : Rel ℤ zero
Coprime = ℕ.Coprime on ∣_∣

-- If i divides jk and is coprime to j, then it divides k.

coprime-divisor : ∀ i j k → Coprime i j → i ∣ j * k → i ∣ k
coprime-divisor i j k c eq =
  ℕ.coprime-divisor c (subst (ℕ._∣_ ∣ i ∣) (abs-*-commute j k) eq)
