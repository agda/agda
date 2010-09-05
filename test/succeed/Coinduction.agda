{-# OPTIONS --universe-polymorphism #-}

module Coinduction where

open import Common.Level

postulate
  ∞  : ∀ {a} (A : Set a) → Set a
  ♯_ : ∀ {a} {A : Set a} → A → ∞ A
  ♭  : ∀ {a} {A : Set a} → ∞ A → A

{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}
{-# BUILTIN FLAT     ♭  #-}

private

  my-♯ : ∀ {a} {A : Set a} → A → ∞ A
  my-♯ x = ♯ x
