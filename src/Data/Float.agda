------------------------------------------------------------------------
-- The Agda standard library
--
-- Floats
------------------------------------------------------------------------

module Data.Float where

open import Data.Bool.Minimal using (Bool; false; true)
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
open import Relation.Binary.PropositionalEquality.TrustMe
open import Data.String using (String)

postulate
  Float : Set

{-# BUILTIN FLOAT Float #-}

primitive
  primFloatEquality : Float → Float → Bool
  primShowFloat     : Float → String

show : Float → String
show = primShowFloat

_≟_ : (x y : Float) → Dec (x ≡ y)
x ≟ y with primFloatEquality x y
... | true  = yes trustMe
... | false = no whatever
  where postulate whatever : _
