{-# OPTIONS --without-K --safe --no-sized-types --no-guardedness #-}

module Agda.Builtin.Char.Properties where

open import Agda.Builtin.Char
open import Agda.Builtin.Equality

primitive

  primCharToNatInjective : ∀ a b → primCharToNat a ≡ primCharToNat b → a ≡ b
