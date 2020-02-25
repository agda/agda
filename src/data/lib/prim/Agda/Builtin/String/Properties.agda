{-# OPTIONS --without-K --safe --no-sized-types --no-guardedness
            --no-subtyping #-}

module Agda.Builtin.String.Properties where

open import Agda.Builtin.String
open import Agda.Builtin.Equality

primitive

  primStringToListInjective : ∀ a b → primStringToList a ≡ primStringToList b → a ≡ b
