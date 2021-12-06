
open import Agda.Builtin.Unit

module Imports.Issue5583 (_ : ⊤) where

it : ∀ {A : Set} → ⦃ A ⦄ → A
it ⦃ x ⦄ = x

data X : Set where
  instance x : X
