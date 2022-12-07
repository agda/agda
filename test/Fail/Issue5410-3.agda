{-# OPTIONS --cubical-compatible --erasure #-}

variable
  @0 A : Set

data D : Set₁ where
  c : A → D
