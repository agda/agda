{-# OPTIONS --without-K --safe --no-sized-types --no-guardedness
            --no-subtyping #-}

module Agda.Builtin.Reflection.Properties where

open import Agda.Builtin.Reflection
open import Agda.Builtin.Equality

primitive

  primMetaToNatInjective : ∀ a b → primMetaToNat a ≡ primMetaToNat b → a ≡ b
  primQNameToWord64sInjective : ∀ a b → primQNameToWord64s a ≡ primQNameToWord64s b → a ≡ b
