{-# OPTIONS --without-K --safe --no-sized-types --no-guardedness #-}

module Agda.Builtin.Reflection.Properties where

open import Agda.Builtin.Reflection
open import Agda.Builtin.Equality

primitive

  primMetaToNatInjective : ∀ a b → primMetaToNat a ≡ primMetaToNat b → a ≡ b
