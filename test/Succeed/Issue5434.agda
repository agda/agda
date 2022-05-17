{-# OPTIONS --two-level --cubical-compatible #-}

open import Agda.Primitive

data D₁ : SSet → SSet (lsuc lzero) where
  c : (@0 A : SSet) → A → D₁ A

data D₂ : Set → SSet (lsuc lzero) where
  c : (@0 A : Set) → A → D₂ A
