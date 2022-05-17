{-# OPTIONS --cubical-compatible #-}

mutual

  data D : Set → Set₁ where
    c : (@0 A : Set) → _ → D _

  _ : (@0 A : Set) → A → D A
  _ = c
