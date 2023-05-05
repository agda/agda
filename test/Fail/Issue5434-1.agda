{-# OPTIONS --cubical-compatible --erasure #-}

data D : Set → Set₁ where
  c : (@0 A : Set) → D A
