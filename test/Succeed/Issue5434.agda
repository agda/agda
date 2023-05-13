{-# OPTIONS --two-level --cubical-compatible --erasure #-}

data D₁ : SSet → SSet₁ where
  c : (@0 A : SSet) → A → D₁ A

data D₂ : Set → SSet₁ where
  c : (@0 A : Set) → A → D₂ A
