------------------------------------------------------------------------
-- Characters
------------------------------------------------------------------------

module Data.Char where

open import Data.Nat
open import Data.Bool
open import Logic
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- The type

postulate
  Char   : Set

{-# BUILTIN CHAR Char #-}

private
 primitive
  primCharToNat    : Char -> ℕ
  primCharEquality : Char -> Char -> Bool

toNat : Char -> ℕ
toNat = primCharToNat

infix 4 _==_

_==_ : Char -> Char -> Bool
_==_ = primCharEquality

_≟_ : Decidable {Char} _≡_
s₁ ≟ s₂ with s₁ == s₂
... | true  = yes trustMe
  where postulate trustMe : _
... | false = no trustMe
  where postulate trustMe : _

setoid : Setoid
setoid = ≡-setoid Char

decSetoid : DecSetoid
decSetoid = record { setoid = setoid; _≟_ = _≟_ }
