{-# OPTIONS --cubical-compatible #-}

mutual

  record R : Set₁ where
    constructor c
    field
      @0 A : Set
      x    : _

  _ : (@0 A : Set) → A → R
  _ = c
