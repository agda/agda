{-# OPTIONS --without-K --safe --no-sized-types --no-guardedness
            --no-subtyping #-}

module Agda.Builtin.Float.Properties where

open import Agda.Builtin.Float
open import Agda.Builtin.Equality

primitive

  primFloatToWord64Injective : ∀ a b → primFloatToWord64 a ≡ primFloatToWord64 b → a ≡ b
