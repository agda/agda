{-# OPTIONS --without-K --guardedness #-}
module Common.Coinduction where

open import Agda.Builtin.Coinduction public

private
  my-♯ : ∀ {a} {A : Set a} → A → ∞ A
  my-♯ x = ♯ x
