{-# OPTIONS --cubical-compatible --erasure #-}

variable
  @0 A : Set

record D : Set₁ where
  field
    f : A
