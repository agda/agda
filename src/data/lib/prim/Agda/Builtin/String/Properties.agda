{-# OPTIONS --without-K --safe --no-sized-types --no-guardedness #-}

module Agda.Builtin.String.Properties where

open import Agda.Builtin.String
open import Agda.Builtin.Equality

primitive

  primStringToListInjective : ∀ a b → primStringToList a ≡ primStringToList b → a ≡ b
  primStringFromListInjective : ∀ a b → primStringFromList a ≡ primStringFromList b → a ≡ b
