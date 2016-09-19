
module _ where

open import Agda.Builtin.Nat

module Postulates where

  infixl 5 _<*>_

  postulate
    F     : Set → Set
    pure  : ∀ {A} → A → F A
    _<*>_ : ∀ {A B} → F (A → B) → F A → F B

  test₀ : F Nat → F Nat → F Nat
  test₀ a b = (| a + b |)

  test₁ : F Nat
  test₁ = (| 5 |)

  test₂ : F Nat → F Nat
  test₂ a = (| suc a |)

  test₃ : F Nat → F Nat
  test₃ a = (| (_+ 5) a |)

  -- Spaces are required! (Issue #2186)
  test₄ : Nat → Nat
  test₄ |n| = suc (|n| + |n|)

module Params {F : Set → Set}
              (pure : ∀ {A} → A → F A)
              (_<*>_ : ∀ {A B} → F (A → B) → F A → F B) where

  test₀ : F Nat → F Nat → F Nat
  test₀ a b = (| a + b |)

  test₁ : F Nat
  test₁ = (| 5 |)

  test₂ : F Nat → F Nat
  test₂ a = (| suc a |)

  test₃ : F Nat → F Nat
  test₃ a = (| (_+ 5) a |)
