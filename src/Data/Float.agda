------------------------------------------------------------------------
-- The Agda standard library
--
-- Floats
------------------------------------------------------------------------

module Data.Float where

open import Data.Bool hiding (_≟_)
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
open import Relation.Binary.PropositionalEquality.TrustMe

postulate
  Float : Set

{-# BUILTIN FLOAT Float #-}

primitive
  primFloatEquality : Float → Float → Bool

_≟_ : (x y : Float) → Dec (x ≡ y)
x ≟ y with primFloatEquality x y
... | true  = yes trustMe
... | false = no whatever
  where postulate whatever : _
