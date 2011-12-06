------------------------------------------------------------------------
-- The Agda standard library
--
-- Characters
------------------------------------------------------------------------

module Data.Char where

open import Data.Nat using (ℕ)
import Data.Nat.Properties as NatProp
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary
open import Relation.Binary
import Relation.Binary.On as On
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
open import Relation.Binary.PropositionalEquality.TrustMe

------------------------------------------------------------------------
-- The type

postulate
  Char : Set

{-# BUILTIN CHAR Char #-}
{-# COMPILED_TYPE Char Char #-}

------------------------------------------------------------------------
-- Operations

private
 primitive
  primCharToNat    : Char → ℕ
  primCharEquality : Char → Char → Bool

toNat : Char → ℕ
toNat = primCharToNat

infix 4 _==_

_==_ : Char → Char → Bool
_==_ = primCharEquality

_≟_ : Decidable {A = Char} _≡_
s₁ ≟ s₂ with s₁ == s₂
... | true  = yes trustMe
... | false = no whatever
  where postulate whatever : _

setoid : Setoid _ _
setoid = PropEq.setoid Char

decSetoid : DecSetoid _ _
decSetoid = PropEq.decSetoid _≟_

-- An ordering induced by the toNat function.

strictTotalOrder : StrictTotalOrder _ _ _
strictTotalOrder = On.strictTotalOrder NatProp.strictTotalOrder toNat
