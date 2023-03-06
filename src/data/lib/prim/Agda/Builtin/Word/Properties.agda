{-# OPTIONS --cubical-compatible --safe --no-sized-types --no-guardedness --level-universe #-}

module Agda.Builtin.Word.Properties where

open import Agda.Builtin.Word
open import Agda.Builtin.Equality

primitive

  primWord64ToNatInjective : ∀ a b → primWord64ToNat a ≡ primWord64ToNat b → a ≡ b
