{-# OPTIONS --cubical-compatible --safe --universe-polymorphism --no-sized-types
            --guardedness --level-universe --erasure #-}

module Agda.Builtin.Coinduction where

infix 1000 ♯_

postulate
  ∞  : ∀ {@0 a} (A : Set a) → Set a
  ♯_ : ∀ {@0 a} {A : Set a} → A → ∞ A
  ♭  : ∀ {@0 a} {A : Set a} → ∞ A → A

{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}
{-# BUILTIN FLAT     ♭  #-}
